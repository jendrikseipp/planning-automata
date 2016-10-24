#include "scp_generators.h"

#include "abstraction.h"

#include "../option_parser.h"
#include "../plugin.h"

#include "../utils/rng.h"
#include "../utils/rng_options.h"

#include <algorithm>
#include <cassert>

using namespace std;

namespace cost_saturation {
static vector<int> get_default_order(int n) {
    vector<int> indices(n);
    iota(indices.begin(), indices.end(), 0);
    return indices;
}

static void reduce_costs(
    vector<int> &remaining_costs, const vector<int> &saturated_costs) {
    assert(remaining_costs.size() == saturated_costs.size());
    for (size_t i = 0; i < remaining_costs.size(); ++i) {
        int &remaining = remaining_costs[i];
        const int &saturated = saturated_costs[i];
        assert(saturated <= remaining);
        /* Since we ignore transitions from states s with h(s)=INF, all
           saturated costs (h(s)-h(s')) are finite or -INF. */
        assert(saturated != INF);
        if (remaining == INF) {
            // INF - x = INF for finite values x.
        } else if (saturated == -INF) {
            remaining = INF;
        } else {
            remaining -= saturated;
        }
        assert(remaining >= 0);
    }
}

static void print_indexed_vector(const vector<int> &vec) {
    for (size_t i = 0; i < vec.size(); ++i) {
        cout << i << ":" << vec[i] << ", ";
    }
    cout << endl;
}

static vector<vector<int>> compute_saturated_cost_partitioning(
    const vector<unique_ptr<Abstraction>> &abstractions,
    const vector<int> &order,
    const vector<int> &operator_costs) {
    assert(abstractions.size() == order.size());
    const bool debug = false;
    vector<int> remaining_costs = operator_costs;
    vector<vector<int>> h_values_by_abstraction(abstractions.size());
    for (int pos : order) {
        Abstraction &abstraction = *abstractions[pos];
        auto pair = abstraction.compute_goal_distances_and_saturated_costs(
            remaining_costs);
        vector<int> &h_values = pair.first;
        vector<int> &saturated_costs = pair.second;
        if (debug) {
            cout << "h-values: ";
            print_indexed_vector(h_values);
            cout << "saturated costs: ";
            print_indexed_vector(saturated_costs);
        }
        h_values_by_abstraction[pos] = move(h_values);
        reduce_costs(remaining_costs, saturated_costs);
        if (debug) {
            cout << "remaining costs: ";
            print_indexed_vector(remaining_costs);
        }
    }
    return h_values_by_abstraction;
}


RandomSCPGenerator::RandomSCPGenerator(const Options &opts)
    : num_orders(opts.get<int>("orders")),
      rng(utils::parse_rng_from_options(opts)) {
}

CostPartitionings RandomSCPGenerator::get_cost_partitionings(
    const vector<unique_ptr<Abstraction>> &abstractions,
    const vector<int> &costs) const {
    CostPartitionings cost_partitionings;
    vector<int> order = get_default_order(abstractions.size());
    for (int i = 0; i < num_orders; ++i) {
        rng->shuffle(order);
        cost_partitionings.push_back(
            compute_saturated_cost_partitioning(abstractions, order, costs));
    }
    return cost_partitionings;
}

static shared_ptr<SCPGenerator> _parse_random(OptionParser &parser) {
    parser.add_option<int>(
        "orders",
        "number of abstraction orders",
        "1",
        Bounds("1", "infinity"));
    utils::add_rng_options(parser);
    Options opts = parser.parse();
    if (parser.dry_run())
        return nullptr;
    else
        return make_shared<RandomSCPGenerator>(opts);
}

static PluginShared<SCPGenerator> _plugin_random(
    "random", _parse_random);

static PluginTypePlugin<SCPGenerator> _type_plugin(
    "SCPGenerator",
    "Saturated cost partitioning generator.");
}
