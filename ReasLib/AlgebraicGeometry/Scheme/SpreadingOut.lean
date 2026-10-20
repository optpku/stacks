/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.GermInjective

@[expose] public section

/-!
# Spreading Out Scheme Morphisms

Uniqueness and existence of scheme morphisms on open neighborhoods from their behavior on
stalks.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace SpreadingOut

variable {X Y S : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)

/-- 0BX6 (1): two `S`-morphisms from `X` to a scheme locally of finite type over `S` that agree at a
point and on its stalk agree on an open neighborhood of that point. -/
@[stacks 0BX6]
theorem unique_of_locallyOfFiniteType [LocallyOfFiniteType sY]
    (f g : X ⟶ Y) (hf : f ≫ sY = sX) (hg : g ≫ sY = sX) {x : X}
    (e : f x = g x)
    (H : f.stalkMap x =
      Y.presheaf.stalkSpecializes (Inseparable.of_eq e.symm).specializes ≫ g.stalkMap x) :
    ∃ U : X.Opens, x ∈ U ∧ U.ι ≫ f = U.ι ≫ g := sorry

/-- 0BX6 (2): two `S`-morphisms from a germ-injective scheme that agree at a point and on its
stalk agree on an open neighborhood of that point. -/
@[stacks 0BX6]
theorem unique_of_isGermInjective {x : X} [X.IsGermInjectiveAt x]
    (f g : X ⟶ Y) (hf : f ≫ sY = sX) (hg : g ≫ sY = sX)
    (e : f x = g x)
    (H : f.stalkMap x =
      Y.presheaf.stalkSpecializes (Inseparable.of_eq e.symm).specializes ≫ g.stalkMap x) :
    ∃ U : X.Opens, x ∈ U ∧ U.ι ≫ f = U.ι ≫ g := sorry

/-- 0BX6 (5): a compatible local map between stalks spreads to a morphism on an open
neighborhood when the target is locally of finite presentation over the base. -/
@[stacks 0BX6]
theorem exists_of_locallyOfFinitePresentation [LocallyOfFinitePresentation sY]
    {x : X} {y : Y} (e : sX x = sY y)
    (φ : Y.presheaf.stalk y ⟶ X.presheaf.stalk x) [IsLocalHom φ.hom]
    (h : sY.stalkMap y ≫ φ =
      S.presheaf.stalkSpecializes (Inseparable.of_eq e).specializes ≫ sX.stalkMap x) :
    ∃ (U : X.Opens) (hxU : x ∈ U) (f : U.toScheme ⟶ Y),
      Spec.map φ ≫ Y.fromSpecStalk y = U.fromSpecStalkOfMem x hxU ≫ f ∧
        f ≫ sY = U.ι ≫ sX := sorry

/-- 0BX6 (6): a compatible local map between stalks spreads to a morphism on an open
neighborhood when the target is locally of finite type over the base and the source germ is
injective. -/
@[stacks 0BX6]
theorem exists_of_isGermInjective [LocallyOfFiniteType sY] {x : X} [X.IsGermInjectiveAt x]
    {y : Y} (e : sX x = sY y)
    (φ : Y.presheaf.stalk y ⟶ X.presheaf.stalk x) [IsLocalHom φ.hom]
    (h : sY.stalkMap y ≫ φ =
      S.presheaf.stalkSpecializes (Inseparable.of_eq e).specializes ≫ sX.stalkMap x) :
    ∃ (U : X.Opens) (hxU : x ∈ U) (f : U.toScheme ⟶ Y),
      Spec.map φ ≫ Y.fromSpecStalk y = U.fromSpecStalkOfMem x hxU ≫ f ∧
        f ≫ sY = U.ι ≫ sX := sorry

end SpreadingOut

end AlgebraicGeometry
