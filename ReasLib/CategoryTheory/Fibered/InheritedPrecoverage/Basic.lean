/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.MorphismProperty
import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.StronglyCartesian.Pullback.Stability
public import ReasLib.CategoryTheory.Fibered.StronglyCartesian.Property

/-!
# Inherited precoverage on the total category of a fibered category

For a precoverage `J` on `C` and a functor `p : S ⥤ C`, the inherited precoverage on `S`
consists of represented families whose arrows are all strongly cartesian and whose image is
`J`-covering in the base.
-/

@[expose] public section

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

open Limits

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]

namespace Precoverage

/-- The inherited precoverage consists of families whose arrows are
strongly cartesian and whose image is covering in the base. -/
@[stacks 06NU]
def stronglyCartesianLift (J : Precoverage C) (p : S ⥤ C) : Precoverage S :=
  (Functor.IsStronglyCartesian.property p).precoverage ⊓ J.comap p

variable (J : Precoverage C) (p : S ⥤ C)

namespace StronglyCartesianLift

/-- A presieve belongs to `J.stronglyCartesianLift p` exactly when each of its arrows is
strongly cartesian over its image and its image presieve belongs to `J`. -/
@[stacks 06NU "membership in the strongly-cartesian lift"]
theorem mem_iff {x : S} {R : Presieve x} :
    R ∈ J.stronglyCartesianLift p x ↔
      (∀ ⦃y : S⦄ ⦃f : y ⟶ x⦄, R f →
        p.IsStronglyCartesian (p.map f) f) ∧
      R.map p ∈ J (p.obj x) := sorry

/-- Every arrow of a covering presieve in `J.stronglyCartesianLift p` is strongly cartesian
over its image. -/
@[stacks 06NU "arrows of inherited covers are strongly cartesian"]
theorem arrow_isStronglyCartesian
    {x y : S} {R : Presieve x} (hR : R ∈ J.stronglyCartesianLift p x)
    {f : y ⟶ x} (hf : R f) :
    p.IsStronglyCartesian (p.map f) f := sorry

/-- The image of a covering presieve in `J.stronglyCartesianLift p` is a `J`-covering
presieve. -/
@[stacks 06NU "images of inherited covers cover the base"]
theorem map_mem
    {x : S} {R : Presieve x} (hR : R ∈ J.stronglyCartesianLift p x) :
    R.map p ∈ J (p.obj x) := sorry

/-- A represented family belongs to `J.stronglyCartesianLift p` exactly when every arrow is
strongly cartesian and the image family belongs to `J`. -/
@[stacks 06NU]
theorem ofArrows_mem_iff
    {x : S} {ι : Type w} (X : ι → S) (f : ∀ i, X i ⟶ x) :
    Presieve.ofArrows X f ∈ J.stronglyCartesianLift p x ↔
      (∀ i, p.IsStronglyCartesian (p.map (f i)) (f i)) ∧
        Presieve.ofArrows (p.obj ∘ X) (fun i ↦ p.map (f i)) ∈ J (p.obj x) := sorry

/-- The strongly-cartesian lift precoverage contains isomorphisms whenever the base
precoverage does. -/
@[stacks 06NU]
instance hasIsos [J.HasIsos] :
    (J.stronglyCartesianLift p).HasIsos := sorry

/-- The strongly-cartesian lift precoverage admits pullback base change whenever the base
precoverage does and the projection is fibred. -/
@[stacks 06NU]
instance hasPullbacks [J.HasPullbacks] [p.IsFibered] :
    (J.stronglyCartesianLift p).HasPullbacks := sorry

/-- The strongly-cartesian lift precoverage is stable under base change whenever the base
precoverage is. -/
@[stacks 06NU]
instance stableUnderBaseChange
    [J.IsStableUnderBaseChange] [p.IsFibered] :
    (J.stronglyCartesianLift p).IsStableUnderBaseChange := sorry

/-- The strongly-cartesian lift precoverage is stable under composition whenever the base
precoverage is. -/
@[stacks 06NU]
instance isStableUnderComposition
    [J.IsStableUnderComposition] :
    (J.stronglyCartesianLift p).IsStableUnderComposition := sorry

end StronglyCartesianLift

end Precoverage

end CategoryTheory
