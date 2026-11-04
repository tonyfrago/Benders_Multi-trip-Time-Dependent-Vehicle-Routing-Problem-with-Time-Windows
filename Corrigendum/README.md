# Corrigendum: corrected codes and results

This folder accompanies the Corrigendum to:

Fragkogios A., Qiu Y., Saharidis G.K.D., Pardalos P.M. (2024). An accelerated Benders decomposition algorithm for the solution of the multi-trip time-dependent vehicle routing problem with time windows. *European Journal of Operational Research*, 317, 500–514. https://doi.org/10.1016/j.ejor.2024.04.013

## What was corrected

The routine that computes the time-dependent travel times, which is shared by all six methods, contained two coding errors. The models, the valid inequalities and the Benders algorithm described in the paper are not affected. The codes in the root folder of this repository are the original versions used for the published paper and contain these errors.

## Contents

- `Supplementary_material_Corrigendum_EJOR_317_500-514.pdf` (and `.docx`): corrected Tables 2–5 and Fig. 4(a). Values that differ from the published paper are in bold.
- `Corrected_codes/`: the corrected codes used to re-solve all instances (IBM ILOG CPLEX 22.1.1).
  - `MT-TDVRPTW_CPLEX_1_v1_corrected.cpp`, `MT-TDVRPTW_CPLEX_1_VI_v1_corrected.cpp`, `MT-TDVRPTW_CPLEX_2_v1_corrected.cpp`, `MT-TDVRPTW_CPLEX_2_VI_v1_corrected.cpp`: MODEL-1, MODEL-1-VI, MODEL-2, MODEL-2-VI.
  - `MT-TDVRPTW_BENDERS_VI_v12_speedup.cpp`: BENDERS-DSEC-VI-SMS.
  - `MT-TDVRPTW_BENDERS_2_v15_speedup.cpp`: BENDERS-DSEC-VI-SMS-MC.
  - Corrections are marked `[CORRECTED]` in the code. The Benders codes also have file output and unused computations switched off (marked `[SPEEDUP]`); the algorithm is unchanged.
