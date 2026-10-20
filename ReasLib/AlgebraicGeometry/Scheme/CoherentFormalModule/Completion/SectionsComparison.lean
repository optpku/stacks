module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.MixedComponents
public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization.AssociatedPoints

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open Set TopologicalSpace
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/-- For nested ideals in a Noetherian ring complete along the smaller ideal and admitting a
canonical dualizing complex, suppose the local-cohomological dimension is at most an integer
`d ≥ 1`. If the completion of a coherent module on the complement of the larger ideal satisfies
the strict `(1, 1 + d)` inequalities, and each stalk whose point closure meets the smaller ideal's
vanishing locus only inside the larger ideal's vanishing locus has depth at least two, then the
canonical map from global sections to the inverse limit of the positive-power quotient sections
is bijective. -/
@[stacks 0EJ6]
theorem sectionsComparison_bijective_of_strictInequalities
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (S : AffineAlgebraizationSetup A)
    (h_dualizing : CategoryTheory.DerivedCategory.HasCanonicalDualizingComplex A)
    [IsAdicComplete S.I A]
    (d : ℤ) (hd : 1 ≤ d)
    (h_cd : Ideal.LocalCohomology.HasDimensionLE S.I d)
    (F : RingedSpace.Coh (S.U.toScheme).toRingedSpace)
    (h_strict : SatisfiesStrictInequalities S
      ((CoherentCompletion.functor
        (AffineAlgebraizationSetup.idealOnOpen S)).obj F)
      1 (1 + d))
    (h_depth : ∀ x : S.U,
      closure ({S.U.ι x} : Set S.X) ∩ Set.range S.y ⊆ Set.range S.z →
        (2 : ℕ∞) ≤ moduleDepth ((S.U.toScheme).presheaf.stalk x)
          (RingedSpace.stalkModuleCat F.obj x)) :
    Function.Bijective
      (Scheme.CoherentCompletion.sectionsComparison
        (AffineAlgebraizationSetup.idealOnOpen S) F.obj) := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
