/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.Logic.UnivLE
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite limits of flat left Kan extensions of type-valued presheaves

A representably flat functor makes the comma categories indexing its presheaf left Kan
extension filtered. When those categories have small object types, their colimits in `Type w`
commute with finite limits. The category object and morphism universes may vary independently.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w uC vC uD vD

namespace CategoryTheory.Functor

/-- Left Kan extension of type-valued presheaves along the opposite of a representably flat
functor preserves finite limits. The size condition bounds the object types of the comma
categories; the existing Kan-extension instances specify the functor being tested. -/
@[stacks 00X5 "left-exact presheaf inverse image"]
instance typePresheafLan_preservesFiniteLimits
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (F : C ⥤ D) [RepresentablyFlat F] [UnivLE.{max uC vD, w}]
    [∀ P : Cᵒᵖ ⥤ Type w, F.op.HasLeftKanExtension P] :
    PreservesFiniteLimits
      (F.op.lan : (Cᵒᵖ ⥤ Type w) ⥤ Dᵒᵖ ⥤ Type w) := sorry

end CategoryTheory.Functor
