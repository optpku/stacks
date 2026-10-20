module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Inequalities
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion
public import ReasLib.AlgebraicGeometry.Scheme.Noetherian.Open
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.CanonicalExistence
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension
public import Mathlib.Topology.Irreducible

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open Set TopologicalSpace
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/-- Let a Noetherian ring be complete along an ideal and admit a canonical dualizing
complex, with local-cohomological dimension at most an integer `d ≥ 1`. If the
completion of a coherent module on the open complement satisfies the strict
`(1, 1 + d)` inequalities, then a point whose closure meets the closed fiber in
irreducible components both contained and not contained in the smaller closed
subset lies in the open complement and its module stalk has depth at least one. -/
@[stacks 0EJ5]
theorem moduleDepth_stalk_ge_one_of_mixed_components
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (S : AffineAlgebraizationSetup A)
    (h_dualizing : CategoryTheory.DerivedCategory.HasCanonicalDualizingComplex A)
    [IsAdicComplete S.I A]
    (d : ℤ) (hd : 1 ≤ d)
    (h_cd : Ideal.LocalCohomology.HasDimensionLE S.I d)
    (F : RingedSpace.Coh (S.U.toScheme).toRingedSpace)
    (h_strict : SatisfiesStrictInequalities S
      ((CoherentCompletion.functor
        ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)).obj F)
      1 (1 + d))
    (x : S.X)
    (h_components :
      let WY := closure ({x} : Set S.X) ∩ Set.range S.y
      ∃ W_in W_out : Set S.X,
        Maximal (fun C ↦ IsIrreducible C ∧ C ⊆ WY) W_in ∧
          Maximal (fun C ↦ IsIrreducible C ∧ C ⊆ WY) W_out ∧
            W_in ⊆ Set.range S.z ∧ ¬ W_out ⊆ Set.range S.z) :
    ∃ hx : x ∈ S.U,
      (1 : ℕ∞) ≤ moduleDepth ((S.U.toScheme).presheaf.stalk ⟨x, hx⟩)
        (RingedSpace.stalkModuleCat F.obj ⟨x, hx⟩) := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
