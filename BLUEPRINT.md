# Blueprint: paper statements, proofs, formalization, finite checks

Paper: `paper/main_v13.tex` (public build). Theorem numbers are those of the PDF (the anonymous build has the same
numbers). Every row is checked by `tools/check_blueprint.py` (labels exist in the TeX sources or in the label list of
the build, numbers agree with the label list, Lean declarations exist in `lean/ApnCipher/`, finite-check files exist).

Columns. **paper**: where the proof is. **Lean**: declarations that are machine-checked (Lean 4.31.0-rc1,
Mathlib d568c8c09630de097a046763c17b9ea99f95f950, standard axioms only). A Lean entry covers exactly what the
`scope` column says, not the whole statement. **finite**: the checker in `checks/`, or the row directory in `evidence/` (its `README.md` is listed;
index `EVIDENCE_COVERAGE.tsv`) that holds the scripts, inputs and recorded outputs (a finite check is not a proof). **kind**: `paper` = proof on paper only; `paper+lean` = the stated part is also machine-checked;
`lean-negative` = a machine-checked statement that a former specialization is vacuous.

| label | no. | paper | Lean | scope of the Lean part | finite | kind |
|---|---|---|---|---|---|---|
| lem:add | 2.1 | Sec. 2 | DigitSplit_v2.phi4_add | additive group of (Z/4)^m with the digit split; the polynomial basis of GR(4,m) is on paper | - | paper+lean |
| thm:eps | 3.4 | Sec. 3 | OneRound.dp_pdB_le; CarryZ.ddtC_pdB_Z_le; CarryE_v2.ddtC_pdB_E_le; CarryPD.ddtC_pdB_G_le | all directions, concrete carry coordinates | evidence/eps/README.md | paper+lean |
| prop:table | 3.5 | Sec. 3 | ColsB_v3.colB_ZZ; ColsB_v3.colB_ZE; ColsB_v3.colB_EZ; ColsB_v3.colB_EE; ColsB_v3.entB_GZ; ColsB_v3.entB_GE; ColsF_v2.colF_Z; ColsF_v2.colF_E; ColsF_v2.entF_G | weight-one kernel direction (omega = 2); general omega on paper | - | paper+lean |
| thm:S | 3.6 | Sec. 3 | TwoStep.two_step_abstract; TwoStep.two_step_pd; WarmStart.edp2_le_four_div_N | one step from the warm start (t = 1); t >= 2 on paper | - | paper+lean |
| thm:W2 | 3.7 | Sec. 3 | Bridge.avgDP_S2_eq; Bridge.avgDP_S2_le | part (1), weight-one rho: real key average <= 4/N; part (2) on paper | evidence/W2/README.md | paper+lean |
| thm:UE | 3.9 | Sec. 3 | - | - | evidence/UE/README.md | paper |
| lem:norm | 4.2 | Sec. 4 | - | - | evidence/general_d/README.md | paper |
| thm:cert | 4.5 | Sec. 4 | RepairLink_v2.ellD; RepairCore_v2.coeff_not_both_zero; RepairCore_v2.nonzero_count_ge | linearity of the actual l_d; power sums p2, p3 on paper | evidence/repair_d0/README.md | paper+lean |
| thm:repair | 4.6 | Sec. 4 | RepairLink_v2.ellD_repair; RepairLink_v2.ellD_one_failure; RepairLink_v2.ellD_pass_count | with hypothesis l_d(g_d) = 1 (proved on paper) | evidence/general_d/README.md | paper+lean |
| prop:mc | 4.9 | Sec. 4 | - | - | checks/p805_p806.py | paper |
| prop:affine | 4.7 | Sec. 4 | - | - | evidence/general_d/README.md | paper |
| tab:cost | 9 | Sec. 7 (bit-model counts) | - | - | evidence/cost_p413/README.md; evidence/cost_F_ha3/README.md; checks/p805_p806.py | paper |
| ex:quant | 4.13 | Sec. 4 | - | - | checks/p805_p806.py | paper |
| lem:reset | 5.1 | Sec. 5 | ResetCompose.sum_reset_ddt; W2Bridge.sum_reset_ddt | any finite abelian group | - | paper+lean |
| lem:D1 | 5.2 | Sec. 5 | MixAdd.mds2A_le; W2Bridge.mds2_le | additive mixer with bijective partial maps (MixAdd); ring-scalar form (W2Bridge) | - | paper+lean |
| thm:P4 | 5.3 | Sec. 5 | ThetaZ4_v3.w2_Z4_theta_le; ThetaZ4_v3.w2_Z4_theta5_le; MixAdd.w2A_split_tail_le | part (1), w = 2, (2,2,1,1), mixer (x,y) -> (x+y, x+Theta y) on (Z/4)^m; general w on paper | - | paper+lean |
| thm:V | 5.7 | Sec. 5 | - | - | evidence/V/README.md; evidence/V3/README.md | paper |
| prop:pf | 6.1 | Sec. 6 | - | - | evidence/pf/README.md | paper |
| thm:R1 | 6.2 | Sec. 6 | - | - | evidence/R1/README.md | paper |
| prop:Zexact | 6.3 | Sec. 6 | - | - | checks/p802_zexact.py | paper |
| thm:G | 6.4 | Sec. 6 | - | - | evidence/G_Minv/README.md | paper |
| prop:Minv | 6.5 | Sec. 6 | - | - | evidence/G_Minv/README.md | paper |
| cor:half | 6.6 | Sec. 6 | - | - | - | paper |
| thm:steps | 6.9 | Sec. 6, App. A | - | - | checks/p803_steps_v2.py | paper |
| prop:condsteps | 6.10 | Sec. 6 | - | - | checks/p803_steps_v2.py | paper |
| cor:inv13 | 6.11 | Sec. 6 | - | - | checks/p803_steps_v2.py | paper |
| rem:theta | 7.1 | Sec. 7 | ThetaZ4_v3.theta5; ThetaZ4_v3.theta5_mixer_mds | m = 5 witness only; general m on paper | evidence/theta/README.md | paper+lean |
| (former specialization) | - | Sec. 7 | VacuousZ4.w2_Z4_mixer_hyps_false; VacuousZ4.no_unit_mds_Z4m | unit-entry, unit-determinant mixers do not exist in the pointwise ring (Z/4)^m | - | lean-negative |

Not formalized: Theorems 3.7(2) (general omega), 3.9, 5.7, all of Section 6, the power sums of Section 4, general w.
The mixer of Theorem 5.3 in Lean is an additive automorphism of (Z/4)^m x (Z/4)^m; the identification with the
mixer [[1,1],[1,t]] of GR(4,m) (multiplication by t = companion matrix of the lifted modulus) is Remark 7.1 (paper,
with exact finite checks for 2 <= m <= 8).
