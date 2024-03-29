#ifndef COST_SATURATION_SATURATED_COST_PARTITIONING_HEURISTIC_H
#define COST_SATURATION_SATURATED_COST_PARTITIONING_HEURISTIC_H

#include "types.h"

#include <vector>

namespace plugins {
class Feature;
class Options;
}

namespace cost_saturation {
class CostPartitioningHeuristic;

enum class Saturator {
    ALL,
    PERIM,
    PERIMSTAR,
};

extern CostPartitioningHeuristic compute_saturated_cost_partitioning(
    const Abstractions &abstractions,
    const std::vector<int> &order,
    std::vector<int> &remaining_costs,
    const std::vector<int> &abstract_state_ids);

extern CostPartitioningHeuristic compute_perim_saturated_cost_partitioning(
    const Abstractions &abstractions,
    const std::vector<int> &order,
    std::vector<int> &remaining_costs,
    const std::vector<int> &abstract_state_ids);

extern void add_saturator_option(plugins::Feature &feature);
extern CPFunction get_cp_function_from_options(const plugins::Options &options);
}

#endif
