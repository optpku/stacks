/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap52.Lemma_52_12_4
public import stacks_project.Chap52.Lemma_52_19_4
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open Set TopologicalSpace
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/-- Lemma 52.19.5: in Situation 52.16.1, let `F` be coherent on `S.U` and let
`d ≥ 1`. If `A` is `S.I`-adically complete, has a dualizing complex, and
`cd(A, S.I) ≤ d`, the canonical completion of `F` satisfies the strict
`(1, 1 + d)`-inequalities, and every stalk whose point closure meets `S.Y` only
inside `S.Z` has depth at least two, then the canonical map from `H⁰(S.U, F)`
to the inverse limit of the positive ideal-power quotient sections is bijective. -/
@[stacks 0EJ6]
theorem sectionsComparison_bijective_of_strictInequalities
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (S : AffineAlgebraizationSetup A)
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)
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
