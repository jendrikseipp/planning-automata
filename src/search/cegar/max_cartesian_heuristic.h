#ifndef CEGAR_MAX_CARTESIAN_HEURISTIC_H
#define CEGAR_MAX_CARTESIAN_HEURISTIC_H

#include "../heuristic.h"

#include <vector>

namespace cegar {
class Abstraction;
class RefinementHierarchy;

/*
  Compute maximum over a set of additive cost partitionings.
*/
class MaxCartesianHeuristic : public Heuristic {
    const std::vector<std::shared_ptr<RefinementHierarchy>> refinement_hierarchies;
    const std::vector<std::vector<std::vector<int>>> h_values_by_orders;

    int compute_max(
        const std::vector<int> &local_state_ids,
        const std::vector<std::vector<std::vector<int>>> &h_values_by_order) const;

protected:
    virtual int compute_heuristic(const GlobalState &global_state);
    int compute_heuristic(const State &state);

public:
    MaxCartesianHeuristic(
        const options::Options &opts,
        std::vector<std::shared_ptr<RefinementHierarchy>> &&refinement_hierarchies,
        std::vector<std::vector<std::vector<int>>> &&h_values_by_orders);
};

std::vector<std::vector<std::vector<int>>>
compute_saturated_cost_partitionings(
    const std::vector<std::unique_ptr<Abstraction>> &abstractions,
    const std::vector<int> operator_costs,
    int num_orders);
}

#endif
