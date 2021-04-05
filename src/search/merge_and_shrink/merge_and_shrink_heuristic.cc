#include "merge_and_shrink_heuristic.h"

#include "distances.h"
#include "factored_transition_system.h"
#include "label_equivalence_relation.h"
#include "labels.h"
#include "merge_and_shrink_algorithm.h"
#include "merge_and_shrink_representation.h"
#include "transition_system.h"
#include "types.h"

#include "../option_parser.h"
#include "../plugin.h"

#include "../task_utils/task_properties.h"

#include "../utils/logging.h"
#include "../utils/markup.h"
#include "../utils/system.h"

#include <cassert>
#include <fstream>
#include <iostream>
#include <utility>

using namespace std;
using utils::ExitCode;

namespace merge_and_shrink {
static void print_vector(const vector<int> &vec, ofstream &out) {
    for (int value : vec) {
        out << value << " ";
    }
    out << endl;
}

static void write_automata_file(
    const TaskProxy &task_proxy, const FactoredTransitionSystem &fts, ofstream &out) {
    int num_operators = fts.get_labels().get_size();
    out << "Actions: " << num_operators << endl;
    int num_automata = fts.get_num_active_entries();
    out << "Automata: " << num_automata << endl;
    out << endl;
    for (auto active_index : fts) {
        const TransitionSystem &ts = fts.get_transition_system(active_index);
        int num_states = ts.get_size();
        out << num_states << endl;
        out << ts.get_init_state() << endl;

        int num_goal_states = 0;
        for (int i = 0; i < num_states; ++i) {
            if (ts.is_goal_state(i)) {
                ++num_goal_states;
            }
        }
        out << num_goal_states << " ";
        for (int i = 0; i < num_states; ++i) {
            if (ts.is_goal_state(i)) {
                out << " " << i;
            }
        }
        out << endl;

        int label_group_id = 0;
        int num_global_actions = 0;
        vector<int> global_to_local_map(num_operators, -1);
        for (GroupAndTransitions gat : ts) {
            const LabelGroup &label_group = gat.label_group;
            for (int label : label_group) {
                global_to_local_map[label] = label_group_id;
                ++num_global_actions;
            }

            ++label_group_id;
        }
        if (num_global_actions != num_operators) {
            ABORT("number of labels differs from number of operators");
        }

        int num_local_actions = label_group_id;

        // For each local state s (rows) and for each local action o (columns):
        // id of state to which we transition from s on o (-1 indicates no transition).
        vector<vector<int>> transition_function(num_states);
        for (auto &dest_states: transition_function) {
            dest_states.resize(num_local_actions, -1);
        }

        label_group_id = 0;
        vector<int> local_action_costs(num_local_actions, -1);
        for (GroupAndTransitions gat : ts) {
            const LabelGroup &label_group = gat.label_group;
            const vector<Transition> &transitions = gat.transitions;

            local_action_costs[label_group_id] = label_group.get_cost();

            for (const Transition &transition : transitions) {
                transition_function[transition.src][label_group_id] = transition.target;
            }

            ++label_group_id;
        }

        out << num_local_actions << endl;

        // Map global actions to local actions.
        print_vector(global_to_local_map, out);

        for (auto &transitions : transition_function) {
            print_vector(transitions, out);
        }

        // Local action costs flag (1 if local actions have different costs; 0 otherwise).
        bool non_unit_cost = !task_properties::is_unit_cost(task_proxy);
        out << non_unit_cost << endl;

        if (non_unit_cost) {
            // For each local action print its integer cost.
            print_vector(local_action_costs, out);
        }
        out << endl;
    }
}

MergeAndShrinkHeuristic::MergeAndShrinkHeuristic(const options::Options &opts)
    : Heuristic(opts),
      verbosity(opts.get<utils::Verbosity>("verbosity")) {
    utils::g_log << "Initializing merge-and-shrink heuristic..." << endl;
    MergeAndShrinkAlgorithm algorithm(opts);
    FactoredTransitionSystem fts = algorithm.build_factored_transition_system(task_proxy);

    // Write automata file.
    ofstream outfile("automata.txt");
    if (outfile.rdstate() & ofstream::failbit) {
        cerr << "Failed to open automata file." << endl;
        utils::exit_with(utils::ExitCode::SEARCH_CRITICAL_ERROR);
    }
    write_automata_file(task_proxy, fts, outfile);
    outfile.close();
    exit(0);

    extract_factors(fts);
    utils::g_log << "Done initializing merge-and-shrink heuristic." << endl << endl;
}

void MergeAndShrinkHeuristic::extract_factor(
    FactoredTransitionSystem &fts, int index) {
    /*
      Extract the factor at the given index from the given factored transition
      system, compute goal distances if necessary and store the M&S
      representation, which serves as the heuristic.
    */
    auto final_entry = fts.extract_factor(index);
    unique_ptr<MergeAndShrinkRepresentation> mas_representation = move(final_entry.first);
    unique_ptr<Distances> distances = move(final_entry.second);
    if (!distances->are_goal_distances_computed()) {
        const bool compute_init = false;
        const bool compute_goal = true;
        distances->compute_distances(compute_init, compute_goal, verbosity);
    }
    assert(distances->are_goal_distances_computed());
    mas_representation->set_distances(*distances);
    mas_representations.push_back(move(mas_representation));
}

bool MergeAndShrinkHeuristic::extract_unsolvable_factor(FactoredTransitionSystem &fts) {
    /* Check if there is an unsolvable factor. If so, extract and store it and
       return true. Otherwise, return false. */
    for (int index : fts) {
        if (!fts.is_factor_solvable(index)) {
            mas_representations.reserve(1);
            extract_factor(fts, index);
            if (verbosity >= utils::Verbosity::NORMAL) {
                utils::g_log << fts.get_transition_system(index).tag()
                             << "use this unsolvable factor as heuristic."
                             << endl;
            }
            return true;
        }
    }
    return false;
}

void MergeAndShrinkHeuristic::extract_nontrivial_factors(FactoredTransitionSystem &fts) {
    // Iterate over remaining factors and extract and store the nontrivial ones.
    for (int index : fts) {
        if (fts.is_factor_trivial(index)) {
            if (verbosity >= utils::Verbosity::VERBOSE) {
                utils::g_log << fts.get_transition_system(index).tag()
                             << "is trivial." << endl;
            }
        } else {
            extract_factor(fts, index);
        }
    }
}

void MergeAndShrinkHeuristic::extract_factors(FactoredTransitionSystem &fts) {
    /*
      TODO: This method has quite a bit of fiddling with aspects of
      transition systems and the merge-and-shrink representation (checking
      whether distances have been computed; computing them) that we would
      like to have at a lower level. See also the TODO in
      factored_transition_system.h on improving the interface of that class
      (and also related classes like TransitionSystem etc).
    */
    assert(mas_representations.empty());

    int num_active_factors = fts.get_num_active_entries();
    if (verbosity >= utils::Verbosity::NORMAL) {
        utils::g_log << "Number of remaining factors: " << num_active_factors << endl;
    }

    bool unsolvalbe = extract_unsolvable_factor(fts);
    if (!unsolvalbe) {
        extract_nontrivial_factors(fts);
    }

    int num_factors_kept = mas_representations.size();
    if (verbosity >= utils::Verbosity::NORMAL) {
        utils::g_log << "Number of factors kept: " << num_factors_kept << endl;
    }
}

int MergeAndShrinkHeuristic::compute_heuristic(const State &ancestor_state) {
    State state = convert_ancestor_state(ancestor_state);
    int heuristic = 0;
    for (const unique_ptr<MergeAndShrinkRepresentation> &mas_representation : mas_representations) {
        int cost = mas_representation->get_value(state);
        if (cost == PRUNED_STATE || cost == INF) {
            // If state is unreachable or irrelevant, we encountered a dead end.
            return DEAD_END;
        }
        heuristic = max(heuristic, cost);
    }
    return heuristic;
}

static shared_ptr<Heuristic> _parse(options::OptionParser &parser) {
    parser.document_synopsis(
        "Merge-and-shrink heuristic",
        "This heuristic implements the algorithm described in the following "
        "paper:" + utils::format_conference_reference(
            {"Silvan Sievers", "Martin Wehrle", "Malte Helmert"},
            "Generalized Label Reduction for Merge-and-Shrink Heuristics",
            "https://ai.dmi.unibas.ch/papers/sievers-et-al-aaai2014.pdf",
            "Proceedings of the 28th AAAI Conference on Artificial"
            " Intelligence (AAAI 2014)",
            "2358-2366",
            "AAAI Press",
            "2014") + "\n" +
        "For a more exhaustive description of merge-and-shrink, see the journal "
        "paper" + utils::format_journal_reference(
            {"Malte Helmert", "Patrik Haslum", "Joerg Hoffmann", "Raz Nissim"},
            "Merge-and-Shrink Abstraction: A Method for Generating Lower Bounds"
            " in Factored State Spaces",
            "https://ai.dmi.unibas.ch/papers/helmert-et-al-jacm2014.pdf",
            "Journal of the ACM",
            "61 (3)",
            "16:1-63",
            "2014") + "\n" +
        "Please note that the journal paper describes the \"old\" theory of "
        "label reduction, which has been superseded by the above conference "
        "paper and is no longer implemented in Fast Downward.\n\n"
        "The following paper describes how to improve the DFP merge strategy "
        "with tie-breaking, and presents two new merge strategies (dyn-MIASM "
        "and SCC-DFP):" + utils::format_conference_reference(
            {"Silvan Sievers", "Martin Wehrle", "Malte Helmert"},
            "An Analysis of Merge Strategies for Merge-and-Shrink Heuristics",
            "https://ai.dmi.unibas.ch/papers/sievers-et-al-icaps2016.pdf",
            "Proceedings of the 26th International Conference on Automated "
            "Planning and Scheduling (ICAPS 2016)",
            "294-298",
            "AAAI Press",
            "2016") + "\n" +
        "Details of the algorithms and the implementation are described in the "
        "paper" + utils::format_conference_reference(
            {"Silvan Sievers"},
            "Merge-and-Shrink Heuristics for Classical Planning: Efficient "
            "Implementation and Partial Abstractions",
            "https://ai.dmi.unibas.ch/papers/sievers-socs2018.pdf",
            "Proceedings of the 11th Annual Symposium on Combinatorial Search "
            "(SoCS 2018)",
            "90-98",
            "AAAI Press",
            "2018")
        );
    parser.document_language_support("action costs", "supported");
    parser.document_language_support("conditional effects", "supported (but see note)");
    parser.document_language_support("axioms", "not supported");
    parser.document_property("admissible", "yes (but see note)");
    parser.document_property("consistent", "yes (but see note)");
    parser.document_property("safe", "yes");
    parser.document_property("preferred operators", "no");
    parser.document_note(
        "Note",
        "Conditional effects are supported directly. Note, however, that "
        "for tasks that are not factored (in the sense of the JACM 2014 "
        "merge-and-shrink paper), the atomic transition systems on which "
        "merge-and-shrink heuristics are based are nondeterministic, "
        "which can lead to poor heuristics even when only perfect shrinking "
        "is performed.");
    parser.document_note(
        "Note",
        "When pruning unreachable states, admissibility and consistency is "
        "only guaranteed for reachable states and transitions between "
        "reachable states. While this does not impact regular A* search which "
        "will never encounter any unreachable state, it impacts techniques "
        "like symmetry-based pruning: a reachable state which is mapped to an "
        "unreachable symmetric state (which hence is pruned) would falsely be "
        "considered a dead-end and also be pruned, thus violating optimality "
        "of the search.");
    parser.document_note(
        "Note",
        "When using a time limit on the main loop of the merge-and-shrink "
        "algorithm, the heuristic will compute the maximum over all heuristics "
        "induced by the remaining factors if terminating the merge-and-shrink "
        "algorithm early. Exception: if there is an unsolvable factor, it will "
        "be used as the exclusive heuristic since the problem is unsolvable.");
    parser.document_note(
        "Note",
        "A currently recommended good configuration uses bisimulation "
        "based shrinking, the merge strategy SCC-DFP, and the appropriate "
        "label reduction setting (max_states has been altered to be between "
        "10k and 200k in the literature):\n"
        "{{{\nmerge_and_shrink(shrink_strategy=shrink_bisimulation(greedy=false),"
        "merge_strategy=merge_sccs(order_of_sccs=topological,merge_selector="
        "score_based_filtering(scoring_functions=[goal_relevance,dfp,"
        "total_order])),label_reduction=exact(before_shrinking=true,"
        "before_merging=false),max_states=50k,threshold_before_merge=1)\n}}}\n");

    Heuristic::add_options_to_parser(parser);
    add_merge_and_shrink_algorithm_options_to_parser(parser);
    options::Options opts = parser.parse();
    if (parser.help_mode()) {
        return nullptr;
    }

    handle_shrink_limit_options_defaults(opts);

    if (parser.dry_run()) {
        return nullptr;
    } else {
        return make_shared<MergeAndShrinkHeuristic>(opts);
    }
}

static options::Plugin<Evaluator> _plugin("merge_and_shrink", _parse);
}
