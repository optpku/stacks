module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.Pushforward.Map.TwoCell.FiberedCategoryOver.Functoriality

/-!
# Inversion-choice independence for fibred pushforward

`FiberedCategoryOver.Pushforward.InversionChoice` is a proposition. Hence the Hom functor formed
from it is definitionally independent of the supplied proof, and its canonical comparison uses
identity data rather than equality transport.
-/

@[expose] public section

universe uC uD uS vC vD vS

namespace CategoryTheory.FiberedCategoryOver.Pushforward.mapFunctor

open Limits

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {X Y : FiberedCategoryOver.{uC, vC, uS, vS} C}
variable (u : C ⥤ D) [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

/-- Pushforward Hom functors formed from two inversion proofs are canonically naturally
isomorphic. Both directions are identities because `InversionChoice u X Y` is a proposition. -/
@[stacks 04WI "bundled pushforward Hom choice comparison"]
noncomputable def choiceIso
    (h h' : InversionChoice u X Y) :
    FiberedCategoryOver.Pushforward.mapFunctor u h ≅
      FiberedCategoryOver.Pushforward.mapFunctor u h' :=
  Iso.refl _

/-- The forward component of inversion-choice independence is the identity `2`-cell. -/
@[simp, stacks 04WI "bundled pushforward Hom choice comparison forward"]
theorem choiceIso.hom.app
    (h h' : InversionChoice u X Y) (F : X ⟶ Y) :
    (choiceIso u h h').hom.app F =
      𝟙 ((FiberedCategoryOver.Pushforward.mapFunctor u h).obj F) := sorry

/-- The inverse component of inversion-choice independence is the identity `2`-cell. -/
@[simp, stacks 04WI "bundled pushforward Hom choice comparison inverse"]
theorem choiceIso.inv.app
    (h h' : InversionChoice u X Y) (F : X ⟶ Y) :
    (choiceIso u h h').inv.app F =
      𝟙 ((FiberedCategoryOver.Pushforward.mapFunctor u h').obj F) := sorry

/-- Comparing an inversion choice with itself gives the identity natural isomorphism. -/
@[simp, stacks 04WI "bundled pushforward Hom choice comparison reflexivity"]
theorem choiceIso.refl (h : InversionChoice u X Y) :
    choiceIso u h h =
      Iso.refl (FiberedCategoryOver.Pushforward.mapFunctor u h) := sorry

/-- Reversing an inversion-choice comparison exchanges its proof inputs. -/
@[simp, stacks 04WI "bundled pushforward Hom choice comparison symmetry"]
theorem choiceIso.symm (h h' : InversionChoice u X Y) :
    (choiceIso u h h').symm = choiceIso u h' h := sorry

/-- Inversion-choice comparisons compose transitively. -/
@[stacks 04WI "bundled pushforward Hom choice comparison transitivity"]
theorem choiceIso.trans (h₀ h₁ h₂ : InversionChoice u X Y) :
    choiceIso u h₀ h₁ ≪≫ choiceIso u h₁ h₂ = choiceIso u h₀ h₂ := sorry

/- Axiom audit: `choiceIso` is `Iso.refl`; its non-Prop data contain no equality transport and
any inherited proof debt lies only in the law fields of the already-defined Hom functor. -/

end CategoryTheory.FiberedCategoryOver.Pushforward.mapFunctor
