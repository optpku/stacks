module

public import ReasLib.CategoryTheory.Fibered.Pushforward.Map.TwoCell
public import ReasLib.CategoryTheory.Fibered.Stack.Hom
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pushforward on morphisms of stacks

Localized pushforward acts on the ambient fibred-category morphisms underlying
two stacks even though the pushed-forward objects need not themselves be
stacks.  This module exposes that Hom functor and its direct computation API.
-/

@[expose] public section

universe uC uD vC vD w₀ w₁

namespace CategoryTheory

open Limits
open scoped Bicategory

namespace StackOver.Pushforward

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {J : GrothendieckTopology C}

/-- Pushforward on the ambient morphisms underlying a pair of bundled stacks, formed from an
explicit inversion choice on their ambient Hom category. -/
@[stacks 04WI "pushforward on stack morphisms"]
noncomputable def mapFunctor
    (u : C ⥤ D) [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    {X Y : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      X.toFiberedCategoryOver Y.toFiberedCategoryOver) :
    (X ⟶ Y) ⥤
      (FiberedCategoryOver.pushforward u X.toFiberedCategoryOver h.source ⟶
        FiberedCategoryOver.pushforward u Y.toFiberedCategoryOver h.target) :=
  (StackOver.Hom.ambientEquivalence X Y).inverse ⋙
    FiberedCategoryOver.Pushforward.mapFunctor u h

namespace mapFunctor

/-- On objects, pushforward of a stack morphism uses the selected inversion proof for its
underlying fibred-category morphism. -/
@[simp, stacks 04WI "pushforward on stack morphisms"]
theorem obj
    (u : C ⥤ D) [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    {X Y : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      X.toFiberedCategoryOver Y.toFiberedCategoryOver)
    (F : X ⟶ Y) :
    (mapFunctor u h).obj F =
      FiberedCategoryOver.Pushforward.map u (StackOver.Hom.toMor F)
        h.source h.target
        (h.inverts (StackOver.Hom.toMor F)) := sorry

/-- On `2`-morphisms, pushforward of stack morphisms is the canonical
  pushforward of the underlying ambient cell. -/
@[simp, stacks 04WI "pushforward on stack 2-morphisms"]
theorem map
    (u : C ⥤ D) [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    {X Y : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      X.toFiberedCategoryOver Y.toFiberedCategoryOver)
    {F G : X ⟶ Y} (eta : F ⟶ G) :
    (mapFunctor u h).map eta =
      FiberedCategoryOver.Pushforward.map₂ u
        h.source h.target
        (h.inverts (StackOver.Hom.toMor F))
        (h.inverts (StackOver.Hom.toMor G))
        (StackOver.Hom.toMor₂ eta) := sorry

/-- Pushforward on stack morphisms is canonically independent of the supplied inversion proof. -/
@[stacks 04WI "pushforward choice comparison"]
noncomputable def choiceIso
    (u : C ⥤ D) [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    {X Y : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
    (h h' : FiberedCategoryOver.Pushforward.InversionChoice u
      X.toFiberedCategoryOver Y.toFiberedCategoryOver) :
    mapFunctor u h ≅ mapFunctor u h' :=
  Functor.isoWhiskerLeft (StackOver.Hom.ambientEquivalence X Y).inverse
    (FiberedCategoryOver.Pushforward.mapFunctor.choiceIso u h h')

/-- The forward component of stack pushforward inversion-choice independence is the identity. -/
@[simp, stacks 04WI "pushforward choice comparison forward component"]
theorem choiceIso.hom.app
    (u : C ⥤ D) [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    {X Y : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
    (h h' : FiberedCategoryOver.Pushforward.InversionChoice u
      X.toFiberedCategoryOver Y.toFiberedCategoryOver)
    (F : X ⟶ Y) :
    (choiceIso u h h').hom.app F = 𝟙 ((mapFunctor u h).obj F) := sorry

/-- The inverse component of stack pushforward inversion-choice independence is the identity. -/
@[simp, stacks 04WI "pushforward choice comparison inverse component"]
theorem choiceIso.inv.app
    (u : C ⥤ D) [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    {X Y : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
    (h h' : FiberedCategoryOver.Pushforward.InversionChoice u
      X.toFiberedCategoryOver Y.toFiberedCategoryOver)
    (F : X ⟶ Y) :
    (choiceIso u h h').inv.app F = 𝟙 ((mapFunctor u h').obj F) := sorry

/-- Comparing a stack pushforward inversion choice with itself gives the identity. -/
@[simp, stacks 04WI "pushforward choice comparison reflexivity"]
theorem choiceIso.refl
    (u : C ⥤ D) [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    {X Y : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      X.toFiberedCategoryOver Y.toFiberedCategoryOver) :
    choiceIso u h h = Iso.refl (mapFunctor u h) := sorry

/-- Reversing a stack pushforward inversion-choice comparison exchanges its inputs. -/
@[simp, stacks 04WI "pushforward choice comparison symmetry"]
theorem choiceIso.symm
    (u : C ⥤ D) [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    {X Y : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
    (h h' : FiberedCategoryOver.Pushforward.InversionChoice u
      X.toFiberedCategoryOver Y.toFiberedCategoryOver) :
    (choiceIso u h h').symm = choiceIso u h' h := sorry

/-- Stack pushforward inversion-choice comparisons compose transitively. -/
@[stacks 04WI "pushforward choice comparison transitivity"]
theorem choiceIso.trans
    (u : C ⥤ D) [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    {X Y : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
    (h₀ h₁ h₂ : FiberedCategoryOver.Pushforward.InversionChoice u
      X.toFiberedCategoryOver Y.toFiberedCategoryOver) :
    choiceIso u h₀ h₁ ≪≫ choiceIso u h₁ h₂ = choiceIso u h₀ h₂ := sorry

end mapFunctor

-- Data audit: the functor composes the ambient Hom equivalence with the explicitly certified
-- fibred pushforward Hom functor; choice comparison data are inherited identity morphisms.

end StackOver.Pushforward

end CategoryTheory
