module

public import DensityHS
public import Solution
public meta import Lean.Util.CollectAxioms
public meta import Lean.Elab.Command

/-!
# Axiom audit for the current proof import closure

Author and maintainer: Xizhi Liu.

The Challenge module is intentionally not imported. The audit checks every
declaration in the project namespaces against the three standard permitted
axioms, including transitive dependencies.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in env.constants do
    if name.toString.startsWith "DensityHS." ||
        name.toString.startsWith "DensityHSSubmission." then
      let axioms ← Lean.collectAxioms name
      let forbidden := axioms.filter (fun a => !allowed.contains a)
      unless forbidden.isEmpty do
        throwError "Forbidden axioms in {name}: {forbidden}"
      checked := checked + 1
  logInfo m!"Axiom audit passed for {checked} project declarations. Permitted: {allowed}."

#print axioms DensityHSSubmission.weighted_matching_base
#print axioms DensityHSSubmission.weighted_clique_density
#print axioms DensityHS.weighted_clique_cover_bound
#print axioms DensityHS.fractional_strong_duality
#print axioms DensityHS.weighted_complete_cover_bound_nonneg
#print axioms DensityHS.exists_extremalTriple
#print axioms DensityHS.ExtremalTriple.support_classification
#print axioms DensityHS.universal_zero_peeling
#print axioms DensityHS.terminal_cliquePath_bound

#print axioms DensityHSSubmission.finite_clique_density_upper
#print axioms DensityHS.Regularity.finite_density_upper_bound
#print axioms DensityHS.Graphon.kernel_coverNumber_density_bound
#print axioms DensityHS.Graphon.extremal_zero_one_ae
#print axioms DensityHS.Digraph.perfect_fractional_tiling_of_outDegree
#print axioms DensityHS.Analysis.null_polarization

#print axioms DensityHSSubmission.finite_density_theorem
#print axioms DensityHS.density_hajnal_szemeredi
#print axioms DensityHS.Constructions.finite_lower_construction
#print axioms DensityHS.Graphon.exists_minimum_kernel_cover

#print axioms DensityHS.Analysis.bounded_tangent_density_fin

#print axioms DensityHS.Graphon.kernel_tilingNumber_density_bound
#print axioms DensityHS.Graphon.graphonSpace_extremal_iff_active
#print axioms DensityHS.Graphon.kernel_extremal_iff_active
#print axioms DensityHS.Stability.finite_stability
#print axioms DensityHS.Stability.graphon_L1_stability
#print axioms DensityHS.Stability.finite_stability_sequence_unconditional
#print axioms DensityHS.Stability.finite_stability_unique_range_unconditional
#print axioms DensityHS.Rainbow.rainbow_clique_factor
#print axioms DensityHSSubmission.rainbow_clique_factor

#print axioms DensityHSSubmission.finite_stability
#print axioms DensityHSSubmission.graphon_density_theorem
#print axioms DensityHSSubmission.graphon_equality_classification
#print axioms DensityHSSubmission.graphon_L1_stability

#print axioms DensityHS.Graphon.Kernel.exists_unit_representation
