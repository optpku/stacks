/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Completion
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.NormalizedSequence.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Completion

@[expose] public section

open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.NormalizedBlowupSequence

/-- Under the Noetherian local-domain and normal-completion hypotheses, every finite normalized-
blowup sequence over the completion descends to a proper sequence over the original scheme. -/
theorem exists_isBaseChange_of_completion
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    [IsNormalRing (AdicCompletion (maximalIdeal A) A)] :
    let Ahat := AdicCompletion (maximalIdeal A) A
    let g : Spec (.of Ahat) ⟶ Spec (.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A Ahat))
    ∀ {Y : Scheme.{u}} (sHat : NormalizedBlowupSequence (Spec (.of Ahat)) Y),
      ∃ (X : Scheme.{u}) (s : NormalizedBlowupSequence (Spec (.of A)) X),
        s.EveryStepProper ∧ s.IsBaseChange g sHat := sorry

end AlgebraicGeometry.Scheme.NormalizedBlowupSequence
