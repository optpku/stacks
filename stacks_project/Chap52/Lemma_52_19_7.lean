/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap52.Lemma_52_19_6
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open Set TopologicalSpace
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/-- Lemma 52.19.7: under the hypotheses of Situation 52.16.1, a coherent formal
module satisfying the strict `(1, 1 + d)`-inequalities and already known to be a
completion has a coherent preimage whose relevant stalks have depth at least two.
This preimage is unique up to a unique isomorphism compatible with the chosen
completion presentations. -/
@[stacks 0EJ8]
theorem existsUniqueAlgebraizationWithDepth
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (S : AffineAlgebraizationSetup A)
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)
    [IsAdicComplete S.I A]
    (d : ℤ) (hd : 1 ≤ d)
    (h_cd : Ideal.LocalCohomology.HasDimensionLE S.I d)
    (F : CoherentFormalModules S.U.toScheme
      (AffineAlgebraizationSetup.idealOnOpen S))
    (h_isCompletion :
      (CoherentCompletion.functor
        (AffineAlgebraizationSetup.idealOnOpen S)).essImage F)
    (h_strict : SatisfiesStrictInequalities S F 1 (1 + d)) :
    ∃ G : RingedSpace.Coh (S.U.toScheme).toRingedSpace,
      ∃ e : (CoherentCompletion.functor
          (AffineAlgebraizationSetup.idealOnOpen S)).obj G ≅ F,
        (∀ x : S.U,
          closure ({S.U.ι x} : Set S.X) ∩ Set.range S.y ⊆ Set.range S.z →
            (2 : ℕ∞) ≤ moduleDepth ((S.U.toScheme).presheaf.stalk x)
              (RingedSpace.stalkModuleCat G.obj x)) ∧
        ∀ (G' : RingedSpace.Coh (S.U.toScheme).toRingedSpace)
            (e' : (CoherentCompletion.functor
              (AffineAlgebraizationSetup.idealOnOpen S)).obj G' ≅ F),
          (∀ x : S.U,
            closure ({S.U.ι x} : Set S.X) ∩ Set.range S.y ⊆ Set.range S.z →
              (2 : ℕ∞) ≤ moduleDepth ((S.U.toScheme).presheaf.stalk x)
                (RingedSpace.stalkModuleCat G'.obj x)) →
            ∃! i : G ≅ G',
              (CoherentCompletion.functor
                (AffineAlgebraizationSetup.idealOnOpen S)).mapIso i ≪≫ e' = e := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
