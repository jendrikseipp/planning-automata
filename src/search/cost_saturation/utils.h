#ifndef COST_SATURATION_UTILS_H
#define COST_SATURATION_UTILS_H

#include "types.h"

#include <iostream>
#include <vector>

class State;
class TaskProxy;

namespace utils {
class RandomNumberGenerator;
}

namespace cost_saturation {
class CostPartitionedHeuristic;

extern std::vector<int> get_default_order(int num_abstractions);

extern int compute_sum_h(
    const std::vector<int> &local_state_ids,
    const std::vector<std::vector<int>> &h_values_by_abstraction);

extern std::vector<int> get_local_state_ids(
    const Abstractions &abstractions, const State &state);

extern CostPartitionedHeuristic compute_saturated_cost_partitioning(
    const Abstractions &abstractions,
    const std::vector<int> &order,
    const std::vector<int> &costs,
    bool filter_blind_heuristics);

extern CostPartitionedHeuristic compute_cost_partitioning_for_static_order(
    const TaskProxy &task_proxy,
    const std::vector<std::unique_ptr<Abstraction>> &abstractions,
    const std::vector<int> &costs,
    CPFunction cp_function,
    const State &state);

extern std::vector<State> sample_states(
    const TaskProxy &task_proxy,
    const std::function<int (const State &)> &heuristic,
    int num_samples,
    const std::shared_ptr<utils::RandomNumberGenerator> &rng);

extern void reduce_costs(
    std::vector<int> &remaining_costs,
    const std::vector<int> &saturated_costs);

template<typename T>
void print_indexed_vector(const std::vector<T> &vec) {
    for (size_t i = 0; i < vec.size(); ++i) {
        std::cout << i << ":";
        T value = vec[i];
        if (value == INF) {
            std::cout << "inf";
        } else if (value == -INF) {
            std::cout << "-inf";
        } else {
            std::cout << value;
        }
        if (i < vec.size() - 1) {
            std::cout << ", ";
        }
    }
    std::cout << std::endl;
}

extern std::vector<bool> convert_to_bitvector(
    const std::vector<int> &vec, int size);
}

#endif
