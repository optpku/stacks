/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Equivalence.Pseudofunctor.Mapping
public import ReasLib.CategoryTheory.Fibered.Pushforward.Pseudofunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pushforward of equivalences of fibred categories

This leaf specializes the generic equivalence action of a pseudofunctor to pushforward with an
explicit coherent inversion choice, and exposes its forward map, inverse map, unit, and counit in
the application-facing API.
-/

@[expose] public section

universe uC uD vC vD w₀ w₁

namespace CategoryTheory

open Bicategory Limits

namespace FiberedCategoryOver.Pushforward

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable (u : C ⥤ D) [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

/-- Pushforward carries an equivalence of fibred categories over `C` to an equivalence of
their pushforwards over `D`. -/
@[stacks 04WI "pushforward equivalence"]
noncomputable def pseudofunctor.mapEquivalence
    (h : CoherentInversionChoice u)
    {X Y : FiberedCategoryOver.{uC, vC, w₀, w₁} C} (e : X ≌ Y) :
    FiberedCategoryOver.pushforward u X (h.obj X) ≌
      FiberedCategoryOver.pushforward u Y (h.obj Y) :=
  (pseudofunctor u h).mapEquivalence e

/-- The forward morphism of a pushforward equivalence uses the supplied inversion proof. -/
@[simp, stacks 04WI "pushforward equivalence forward map"]
theorem pseudofunctor.mapEquivalence.hom
    (h : CoherentInversionChoice u)
    {X Y : FiberedCategoryOver.{uC, vC, w₀, w₁} C} (e : X ≌ Y) :
    (pseudofunctor.mapEquivalence u h e).hom =
      FiberedCategoryOver.Pushforward.map u e.hom
        (h.obj X) (h.obj Y) (h.inverts e.hom) := sorry

/-- The inverse morphism of a pushforward equivalence uses the supplied inversion proof. -/
@[simp, stacks 04WI "pushforward equivalence inverse map"]
theorem pseudofunctor.mapEquivalence.inv
    (h : CoherentInversionChoice u)
    {X Y : FiberedCategoryOver.{uC, vC, w₀, w₁} C} (e : X ≌ Y) :
    (pseudofunctor.mapEquivalence u h e).inv =
      FiberedCategoryOver.Pushforward.map u e.inv
        (h.obj Y) (h.obj X) (h.inverts e.inv) := sorry

/-- The unit of a pushforward equivalence is the unit supplied by the pushforward
pseudofunctor. -/
@[simp, stacks 04WI "pushforward equivalence unit"]
theorem pseudofunctor.mapEquivalence.unit
    (h : CoherentInversionChoice u)
    {X Y : FiberedCategoryOver.{uC, vC, w₀, w₁} C} (e : X ≌ Y) :
    (pseudofunctor.mapEquivalence u h e).unit =
      Pseudofunctor.mapEquivalence.unitIso (pseudofunctor u h) e := sorry

/-- The counit of a pushforward equivalence is the counit supplied by the pushforward
pseudofunctor. -/
@[simp, stacks 04WI "pushforward equivalence counit"]
theorem pseudofunctor.mapEquivalence.counit
    (h : CoherentInversionChoice u)
    {X Y : FiberedCategoryOver.{uC, vC, w₀, w₁} C} (e : X ≌ Y) :
    (pseudofunctor.mapEquivalence u h e).counit =
      Pseudofunctor.mapEquivalence.counitIso (pseudofunctor u h) e := sorry

end FiberedCategoryOver.Pushforward

end CategoryTheory

-- Data audit: the mapped equivalence is built from `pseudofunctor u h`, so all localization and
-- comparison choices enter through the explicit coherent owner `h`.
