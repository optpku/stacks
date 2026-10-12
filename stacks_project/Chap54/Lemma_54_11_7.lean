/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.NormalizedSequence.Completion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped AlgebraicGeometry

universe u

/- Lemma 54.11.7: every finite sequence of normalized blowups over the completion of a
Noetherian local domain with normal completion descends to a sequence of proper normalized
blowups, and every transition of the original sequence is recovered by base change. -/
@[stacks 0BGA] #check
  (AlgebraicGeometry.Scheme.NormalizedBlowupSequence.exists_isBaseChange_of_completion :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
      [IsNormalRing (AdicCompletion (maximalIdeal A) A)],
      let Ahat := AdicCompletion (maximalIdeal A) A
      let g : Spec (.of Ahat) ⟶ Spec (.of A) :=
        Spec.map (CommRingCat.ofHom (algebraMap A Ahat))
      ∀ {Y : Scheme.{u}} (sHat : AlgebraicGeometry.Scheme.NormalizedBlowupSequence
          (Spec (.of Ahat)) Y),
        ∃ (X : Scheme.{u})
          (s : AlgebraicGeometry.Scheme.NormalizedBlowupSequence (Spec (.of A)) X),
          s.EveryStepProper ∧ s.IsBaseChange g sHat)
