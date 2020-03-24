#include "saturated_cost_partitioning_online_heuristic.h"

#include "abstraction.h"
#include "cost_partitioning_heuristic.h"
#include "diversifier.h"
#include "max_cost_partitioning_heuristic.h"
#include "order_generator.h"
#include "saturated_cost_partitioning_heuristic.h"
#include "utils.h"

#include "../option_parser.h"
#include "../plugin.h"

#include "../task_utils/sampling.h"
#include "../task_utils/task_properties.h"
#include "../utils/countdown_timer.h"
#include "../utils/logging.h"
#include "../utils/rng_options.h"
#include "../utils/timer.h"

using namespace std;

namespace cost_saturation {
static const int IS_NOVEL = -3;
static const int IS_NOT_NOVEL = -4;

static vector<vector<int>> sample_states_and_return_abstract_state_ids(
    const TaskProxy &task_proxy,
    const Abstractions &abstractions,
    sampling::RandomWalkSampler &sampler,
    int num_samples,
    int init_h,
    const DeadEndDetector &is_dead_end,
    double max_sampling_time) {
    assert(num_samples >= 1);
    utils::CountdownTimer sampling_timer(max_sampling_time);
    utils::Log() << "Start sampling" << endl;
    vector<vector<int>> abstract_state_ids_by_sample;
    abstract_state_ids_by_sample.push_back(
        get_abstract_state_ids(abstractions, task_proxy.get_initial_state()));
    while (static_cast<int>(abstract_state_ids_by_sample.size()) < num_samples
           && !sampling_timer.is_expired()) {
        abstract_state_ids_by_sample.push_back(
            get_abstract_state_ids(abstractions, sampler.sample_state(init_h, is_dead_end)));
    }
    utils::Log() << "Samples: " << abstract_state_ids_by_sample.size() << endl;
    utils::Log() << "Sampling time: " << sampling_timer.get_elapsed_time() << endl;
    return abstract_state_ids_by_sample;
}

// TODO: avoid code duplication
static void erase_useless_abstractions(
    const vector<CostPartitioningHeuristic> &cp_heuristics,
    const UnsolvabilityHeuristic &unsolvability_heuristic,
    Abstractions &abstractions) {
    int num_abstractions = abstractions.size();

    // Collect IDs of useful abstractions.
    vector<bool> useful_abstractions(num_abstractions, false);
    unsolvability_heuristic.mark_useful_abstractions(useful_abstractions);
    for (const auto &cp_heuristic : cp_heuristics) {
        cp_heuristic.mark_useful_abstractions(useful_abstractions);
    }

    for (int i = 0; i < num_abstractions; ++i) {
        if (!useful_abstractions[i]) {
            abstractions[i] = nullptr;
        }
    }
}

SaturatedCostPartitioningOnlineHeuristic::SaturatedCostPartitioningOnlineHeuristic(
    const options::Options &opts,
    Abstractions &&abstractions,
    CPHeuristics &&cp_heuristics,
    UnsolvabilityHeuristic &&unsolvability_heuristic)
    : Heuristic(opts),
      order_generator(opts.get<shared_ptr<OrderGenerator>>("orders")),
      cp_function(get_cp_function_from_options(opts)),
      abstractions(move(abstractions)),
      cp_heuristics(move(cp_heuristics)),
      unsolvability_heuristic(move(unsolvability_heuristic)),
      interval(opts.get<int>("interval")),
      max_time(opts.get<double>("max_time")),
      diversify(opts.get<bool>("diversify")),
      num_samples(opts.get<int>("samples")),
      costs(task_properties::get_operator_costs(task_proxy)),
      improve_heuristic(true),
      num_duplicate_orders(0),
      num_evaluated_states(0),
      num_scps_computed(0) {
    if (!diversify) {
        ABORT("Online SCP needs diversify=true.");
    }
    if (opts.get<double>("max_optimization_time") != 0.0) {
        ABORT("Order optimization is not implemented for online SCP.");
    }
    if (opts.get<int>("max_orders") != INF) {
        ABORT("Limiting the number of orders is not implemented for online SCP.");
    }
    fact_id_offsets.reserve(task_proxy.get_variables().size());
    int num_facts = 0;
    for (VariableProxy var : task_proxy.get_variables()) {
        fact_id_offsets.push_back(num_facts);
        num_facts += var.get_domain_size();
    }
    cout << "Fact ID offsets: " << fact_id_offsets << endl;

    if (interval == -1) {
        seen_facts.resize(num_facts, false);
    } else if (interval == -2) {
        seen_fact_pairs.resize(num_facts);
        for (int fact_id = 0; fact_id < num_facts; ++fact_id) {
            seen_fact_pairs[fact_id].resize(num_facts, false);
        }
    }

    setup_diversifier(*utils::parse_rng_from_options(opts));

    compute_heuristic_timer = utils::make_unique_ptr<utils::Timer>(false);
    convert_global_state_timer = utils::make_unique_ptr<utils::Timer>(false);
    improve_heuristic_timer = utils::make_unique_ptr<utils::Timer>(false);
    compute_orders_timer = utils::make_unique_ptr<utils::Timer>(false);
    get_abstract_state_ids_timer = utils::make_unique_ptr<utils::Timer>(false);
    unsolvability_heuristic_timer = utils::make_unique_ptr<utils::Timer>(false);
    compute_max_h_timer = utils::make_unique_ptr<utils::Timer>(false);
    compute_novelty_timer = utils::make_unique_ptr<utils::Timer>(false);
    compute_scp_timer = utils::make_unique_ptr<utils::Timer>(false);
    compute_h_timer = utils::make_unique_ptr<utils::Timer>(false);
    diversification_timer = utils::make_unique_ptr<utils::Timer>(false);
}

SaturatedCostPartitioningOnlineHeuristic::~SaturatedCostPartitioningOnlineHeuristic() {
    print_statistics();
}

void SaturatedCostPartitioningOnlineHeuristic::setup_diversifier(
    utils::RandomNumberGenerator &rng) {
    DeadEndDetector is_dead_end =
        [this](const State &state) {
            return unsolvability_heuristic.is_unsolvable(
                get_abstract_state_ids(abstractions, state));
        };

    State initial_state = task_proxy.get_initial_state();

    // Compute h(s_0) using a greedy order for s_0.
    vector<int> abstract_state_ids_for_init = get_abstract_state_ids(
        abstractions, initial_state);
    Order order_for_init = order_generator->compute_order_for_state(
        abstract_state_ids_for_init, true);
    CostPartitioningHeuristic cp_for_init = cp_function(
        abstractions, order_for_init, costs, abstract_state_ids_for_init);
    int init_h = cp_for_init.compute_heuristic(abstract_state_ids_for_init);

    sampling::RandomWalkSampler sampler(task_proxy, rng);

    double max_sampling_time = max_time / 2;
    diversifier = utils::make_unique_ptr<Diversifier>(
        sample_states_and_return_abstract_state_ids(
            task_proxy, abstractions, sampler, num_samples, init_h, is_dead_end, max_sampling_time));
}

bool SaturatedCostPartitioningOnlineHeuristic::visit_fact_pair(int fact_id1, int fact_id2) {
    if (fact_id1 > fact_id2) {
        swap(fact_id1, fact_id2);
    }
    assert(fact_id1 < fact_id2);
    bool novel = !seen_fact_pairs[fact_id1][fact_id2];
    seen_fact_pairs[fact_id1][fact_id2] = true;
    return novel;
}

bool SaturatedCostPartitioningOnlineHeuristic::is_novel(
    OperatorID op_id, const GlobalState &state) {
    if (interval == -1) {
        bool novel = false;
        for (EffectProxy effect : task_proxy.get_operators()[op_id].get_effects()) {
            FactPair fact = effect.get_fact().get_pair();
            int fact_id = get_fact_id(fact.var, fact.value);
            if (!seen_facts[fact_id]) {
                seen_facts[fact_id] = true;
                novel = true;
            }
        }
        return novel;
    } else if (interval == -2) {
        int num_vars = fact_id_offsets.size();
        bool novel = false;
        for (EffectProxy effect : task_proxy.get_operators()[op_id].get_effects()) {
            FactPair fact1 = effect.get_fact().get_pair();
            int fact_id1 = get_fact_id(fact1.var, fact1.value);
            for (int var2 = 0; var2 < num_vars; ++var2) {
                if (fact1.var == var2) {
                    continue;
                }
                FactPair fact2(var2, state[var2]);
                int fact_id2 = get_fact_id(fact2.var, fact2.value);
                if (visit_fact_pair(fact_id1, fact_id2)) {
                    novel = true;
                }
            }
        }
        return novel;
    } else {
        ABORT("invalid value for interval");
    }
}

void SaturatedCostPartitioningOnlineHeuristic::notify_initial_state(
    const GlobalState &initial_state) {
    if (interval >= 1) {
        return;
    }

    heuristic_cache[initial_state].h = IS_NOVEL;
    int num_vars = fact_id_offsets.size();
    if (interval == -1) {
        for (int var = 0; var < num_vars; ++var) {
            seen_facts[get_fact_id(var, initial_state[var])] = true;
        }
    } else if (interval == -2) {
        for (int var1 = 0; var1 < num_vars; ++var1) {
            int fact_id1 = get_fact_id(var1, initial_state[var1]);
            for (int var2 = var1 + 1; var2 < num_vars; ++var2) {
                int fact_id2 = get_fact_id(var2, initial_state[var2]);
                visit_fact_pair(fact_id1, fact_id2);
            }
        }
    } else {
        ABORT("invalid value for interval");
    }
}

void SaturatedCostPartitioningOnlineHeuristic::notify_state_transition(
    const GlobalState &, OperatorID op_id, const GlobalState &state) {
    if (interval >= 1) {
        return;
    }

    // We only need to compute novelty for new states.
    compute_novelty_timer->reset();
    if (heuristic_cache[state].h == NO_VALUE) {
        if (is_novel(op_id, state)) {
            heuristic_cache[state].h = IS_NOVEL;
        } else {
            heuristic_cache[state].h = IS_NOT_NOVEL;
        }
        assert(heuristic_cache[state].dirty);
    }
    compute_novelty_timer->stop();
}

int SaturatedCostPartitioningOnlineHeuristic::get_fact_id(int var, int value) const {
    return fact_id_offsets[var] + value;
}

bool SaturatedCostPartitioningOnlineHeuristic::should_compute_scp(const GlobalState &global_state) {
    if (interval > 0) {
        return num_evaluated_states % interval == 0;
    } else if (interval == -1 || interval == -2) {
        return heuristic_cache[global_state].h == IS_NOVEL;
    } else {
        ABORT("invalid value for interval");
    }
}

int SaturatedCostPartitioningOnlineHeuristic::compute_heuristic(
    const GlobalState &global_state) {
    compute_heuristic_timer->resume();

    convert_global_state_timer->resume();
    State state = convert_global_state(global_state);
    convert_global_state_timer->stop();

    get_abstract_state_ids_timer->resume();
    vector<int> abstract_state_ids = get_abstract_state_ids(abstractions, state);
    get_abstract_state_ids_timer->stop();

    unsolvability_heuristic_timer->resume();
    if (unsolvability_heuristic.is_unsolvable(abstract_state_ids)) {
        compute_heuristic_timer->stop();
        unsolvability_heuristic_timer->stop();
        return DEAD_END;
    }
    unsolvability_heuristic_timer->stop();

    compute_max_h_timer->resume();
    int max_h = compute_max_h_with_statistics(
        cp_heuristics, abstract_state_ids, num_best_order);
    compute_max_h_timer->stop();

    improve_heuristic_timer->resume();
    if (improve_heuristic && (*improve_heuristic_timer)() > max_time) {
        improve_heuristic = false;
        erase_useless_abstractions(cp_heuristics, unsolvability_heuristic, abstractions);
    }
    if (improve_heuristic && should_compute_scp(global_state)) {
        compute_orders_timer->resume();
        Order order = order_generator->compute_order_for_state(
            abstract_state_ids, num_evaluated_states == 0);
        compute_orders_timer->stop();

        if (seen_orders.count(order)) {
            ++num_duplicate_orders;
        } else {
            compute_scp_timer->resume();
            CostPartitioningHeuristic cost_partitioning =
                cp_function(abstractions, order, costs, abstract_state_ids);
            compute_scp_timer->stop();
            ++num_scps_computed;

            compute_h_timer->resume();
            int h = cost_partitioning.compute_heuristic(abstract_state_ids);
            compute_h_timer->stop();

            max_h = max(max_h, h);

            diversification_timer->resume();
            if (diversifier->is_diverse(cost_partitioning)) {
                cp_heuristics.push_back(move(cost_partitioning));
                cout << "Stored SCPs: " << cp_heuristics.size() << endl;
            }
            diversification_timer->stop();

            seen_orders.insert(move(order));
        }
    }
    improve_heuristic_timer->stop();

    ++num_evaluated_states;
    compute_heuristic_timer->stop();
    return max_h;
}

void SaturatedCostPartitioningOnlineHeuristic::print_statistics() const {
    cout << "Duplicate orders: " << num_duplicate_orders << endl;
    cout << "Computed SCPs: " << num_scps_computed << endl;
    cout << "Stored SCPs: " << cp_heuristics.size() << endl;
    cout << "Time for computing heuristic: " << *compute_heuristic_timer << endl;
    cout << "Time for converting state: " << *convert_global_state_timer << endl;
    cout << "Time for computing abstract state IDs: " << *get_abstract_state_ids_timer << endl;
    cout << "Time for checking unsolvability: " << *unsolvability_heuristic_timer << endl;
    cout << "Time for computing max_h: " << *compute_max_h_timer << endl;
    cout << "Time for improving heuristic: " << *improve_heuristic_timer << endl;
    cout << "Time for computing novelty: " << *compute_novelty_timer << endl;
    cout << "Time for computing orders: " << *compute_orders_timer << endl;
    cout << "Time for computing SCPs: " << *compute_scp_timer << endl;
    cout << "Time for computing h: " << *compute_h_timer << endl;
    cout << "Time for diversification: " << *diversification_timer << endl;
}


static shared_ptr<Heuristic> _parse(OptionParser &parser) {
    parser.document_synopsis(
        "Saturated cost partitioning online heuristic",
        "");

    prepare_parser_for_cost_partitioning_heuristic(parser);
    add_saturator_option(parser);
    add_order_options_to_parser(parser);

    parser.add_option<int>(
        "interval",
        "compute SCP for every interval-th state",
        "1",
        Bounds("-2", "infinity"));

    Options opts = parser.parse();
    if (parser.help_mode())
        return nullptr;

    if (parser.dry_run())
        return nullptr;

    shared_ptr<AbstractTask> task = opts.get<shared_ptr<AbstractTask>>("transform");
    TaskProxy task_proxy(*task);
    vector<int> costs = task_properties::get_operator_costs(task_proxy);
    Abstractions abstractions = generate_abstractions(
        task, opts.get_list<shared_ptr<AbstractionGenerator>>("abstractions"));
    UnsolvabilityHeuristic unsolvability_heuristic(abstractions);
    CPHeuristics cp_heuristics = {};
    shared_ptr<OrderGenerator> order_generator = opts.get<shared_ptr<OrderGenerator>>("orders");
    order_generator->initialize(abstractions, costs);

    return make_shared<SaturatedCostPartitioningOnlineHeuristic>(
        opts,
        move(abstractions),
        move(cp_heuristics),
        move(unsolvability_heuristic));
}

static Plugin<Evaluator> _plugin("scp_online", _parse);
}
