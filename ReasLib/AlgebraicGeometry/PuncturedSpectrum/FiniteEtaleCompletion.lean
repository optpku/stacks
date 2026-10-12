/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.Completion
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.PrincipalQuotient
public import Mathlib.RingTheory.Henselian

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- Restriction of the principal-quotient punctured-spectrum map along maximal-ideal
completion. -/
noncomputable abbrev completedPrincipalRestriction (f : maximalIdeal A) :
    pullback (principalQuotientMap f) (completionMap A) ⟶
      scheme (AdicCompletion (maximalIdeal A) A) :=
  pullback.snd (principalQuotientMap f) (completionMap A)

/-- For a Noetherian local ring and a henselian principal pair, fullness and faithfulness
of finite étale restriction after maximal-ideal completion imply fullness of the original
principal-quotient restriction. -/
instance finiteEtaleBaseChange_full_of_completion (f : maximalIdeal A)
    [HenselianRing A (principalIdeal f)]
    [(Scheme.finiteEtaleBaseChange (completedPrincipalRestriction f)).Full]
    [(Scheme.finiteEtaleBaseChange (completedPrincipalRestriction f)).Faithful] :
    (Scheme.finiteEtaleBaseChange (principalQuotientMap f)).Full := sorry

/-- For a Noetherian local ring and a henselian principal pair, fullness and faithfulness
of finite étale restriction after maximal-ideal completion imply faithfulness of the
original principal-quotient restriction. -/
instance finiteEtaleBaseChange_faithful_of_completion (f : maximalIdeal A)
    [HenselianRing A (principalIdeal f)]
    [(Scheme.finiteEtaleBaseChange (completedPrincipalRestriction f)).Full]
    [(Scheme.finiteEtaleBaseChange (completedPrincipalRestriction f)).Faithful] :
    (Scheme.finiteEtaleBaseChange (principalQuotientMap f)).Faithful := sorry

end AlgebraicGeometry.PuncturedSpectrum
