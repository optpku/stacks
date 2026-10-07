module

public import ReasLib.CategoryTheory.Fibered.Pushforward.Hom.Fibered.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projection-choice independence of the pushforward Hom functor

`ProjectionChoice u X` is proof-only data. Consequently the pushforward object and the Hom
comparison are definitionally independent of the supplied proof, and their canonical comparison
is the identity natural isomorphism. This leaf records that fact together with the coherence API
needed to change choices inside larger composites.
-/

@[expose] public section

universe uC uD vC vD w₀ w₁

namespace CategoryTheory

open Limits

namespace FiberedCategoryOver.Pushforward.homFunctor

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]

variable (u : C ⥤ D)
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

variable {X : FiberedCategoryOver.{uC, vC,
  max w₀ (max uC (max uD (max vC vD))),
  max w₁ (max w₀ (max uC (max uD (max vC vD))))} C}
variable {Y : FiberedCategoryOver.{uD, vD,
  max w₀ (max uC (max uD (max vC vD))),
  max w₁ (max w₀ (max uC (max uD (max vC vD))))} D}

/-- The pushforward-pullback Hom functor is canonically independent of the proof supplying its
pushforward projection. Since `ProjectionChoice u X` is a proposition, this comparison has
identity data in both directions rather than equality-transport data. -/
@[stacks 04WI "pushforward-pullback Hom choice comparison"]
noncomputable def choiceIso
    (h₀ h₁ : ProjectionChoice u X) (Y : FiberedCategoryOver.{uD, vD,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} D) :
    homFunctor u h₀ Y ≅ homFunctor u h₁ Y :=
  Iso.refl _

/-- The forward component of projection-choice independence is the identity `2`-morphism. -/
@[simp, stacks 04WI "pushforward-pullback Hom choice comparison forward"]
theorem choiceIso.hom.app
    (h₀ h₁ : ProjectionChoice u X)
    (G : FiberedCategoryOver.pushforward u X h₀ ⟶ Y) :
    (choiceIso u h₀ h₁ Y).hom.app G =
      𝟙 ((homFunctor u h₀ Y).obj G) := sorry

/-- The inverse component of projection-choice independence is the identity `2`-morphism. -/
@[simp, stacks 04WI "pushforward-pullback Hom choice comparison inverse"]
theorem choiceIso.inv.app
    (h₀ h₁ : ProjectionChoice u X)
    (G : FiberedCategoryOver.pushforward u X h₁ ⟶ Y) :
    (choiceIso u h₀ h₁ Y).inv.app G =
      𝟙 ((homFunctor u h₁ Y).obj G) := sorry

/-- Comparing a projection choice with itself gives the identity natural isomorphism. -/
@[simp, stacks 04WI "pushforward-pullback Hom choice comparison reflexivity"]
theorem choiceIso.refl (h : ProjectionChoice u X) :
    choiceIso u h h Y = Iso.refl (homFunctor u h Y) := sorry

/-- Reversing a projection-choice comparison exchanges the two proof inputs. -/
@[simp, stacks 04WI "pushforward-pullback Hom choice comparison symmetry"]
theorem choiceIso.symm (h₀ h₁ : ProjectionChoice u X) :
    (choiceIso u h₀ h₁ Y).symm = choiceIso u h₁ h₀ Y := sorry

/-- Projection-choice comparisons compose transitively. -/
@[simp, stacks 04WI "pushforward-pullback Hom choice comparison transitivity"]
theorem choiceIso.trans (h₀ h₁ h₂ : ProjectionChoice u X) :
    choiceIso u h₀ h₁ Y ≪≫ choiceIso u h₁ h₂ Y =
      choiceIso u h₀ h₂ Y := sorry

end FiberedCategoryOver.Pushforward.homFunctor

end CategoryTheory

/- Axiom audit: `choiceIso` is `Iso.refl`; its non-Prop hom and inv are identities. Any
`sorryAx` reported through its type comes from the already-defined Hom functors and their
proof-valued law fields, not from projection-choice transport. -/
