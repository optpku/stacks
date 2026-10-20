module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.HomComparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open Set TopologicalSpace
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/- Lemma 52.19.6: in Situation 52.16.1, let `F` be coherent on `S.U` and let
`d ≥ 1`. If `A` is `S.I`-adically complete, has a dualizing complex, and
`cd(A, S.I) ≤ d`, the canonical completion of `F` satisfies the strict
`(1, 1 + d)`-inequalities, and every stalk whose point closure meets `S.Y` only
inside `S.Z` has depth at least two, then canonical completion induces a bijection
from `G ⟶ F` to the morphisms between their completions for every coherent `G`. -/
@[stacks 0EJ7] #check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.homMap_bijective_of_strictInequalities :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
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
          (RingedSpace.stalkModuleCat F.obj x))
    (G : RingedSpace.Coh (S.U.toScheme).toRingedSpace),
    Function.Bijective (fun f : G ⟶ F ↦
      (CoherentCompletion.functor
        (AffineAlgebraizationSetup.idealOnOpen S)).map f))

end AlgebraicGeometry.Scheme.CoherentFormalModules
