#! /bin/bash

set -euo

./build.py && ./fast-downward.py misc/tests/benchmarks/miconic/s1-0.pddl --search "astar(merge_and_shrink(shrink_strategy=shrink_bisimulation(greedy=false),merge_strategy=merge_sccs(order_of_sccs=topological,merge_selector=score_based_filtering(scoring_functions=[goal_relevance(),dfp(),total_order()])),label_reduction=exact(before_shrinking=true,before_merging=false),max_states=50k,threshold_before_merge=1, main_loop_max_time=0, verbosity=normal))"
