/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsClosure
public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.ObjectProperty.FiniteCoproductClosure

@[expose] public section

/-!
# Mapping Object-Property Closures

This leaf contains generic comparisons between mapping an object property along
a functor and applying lattice, retract, or colimit closures.
-/

open CategoryTheory
open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.ObjectProperty

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- Mapping into an isomorphism-closed property is equivalent to objectwise
landing in that property. -/
@[stacks 07A8 "essential-image landing criterion"]
theorem map_le_iff_le_inverseImage (P : ObjectProperty C) (Q : ObjectProperty D)
    [Q.IsClosedUnderIsomorphisms] (F : C ⥤ D) :
    P.map F ≤ Q ↔ P ≤ Q.inverseImage F := sorry

/-- Mapping object properties along a functor preserves arbitrary suprema. -/
@[stacks 0FX5]
theorem map_iSup (F : C ⥤ D) {ι : Sort*} (P : ι → ObjectProperty C) :
    (⨆ i, P i).map F = ⨆ i, (P i).map F := sorry

/-- Mapping a retract closure is contained in the retract closure of the mapped property. -/
@[stacks 0FX5]
theorem map_retractClosure_le (F : C ⥤ D) (P : ObjectProperty C) :
    P.retractClosure.map F ≤ (P.map F).retractClosure := sorry

end

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {α : Type*} (J : α → Type*)
variable [∀ a, Category (J a)]
variable (F : C ⥤ D)
variable [∀ a, PreservesColimitsOfShape (J a) F]

/-- Mapping a colimit closure is contained in the corresponding closure of the mapped property. -/
@[stacks 0FX5]
theorem map_colimitsClosure_le (P : ObjectProperty C) :
    (P.colimitsClosure J).map F ≤ (P.map F).colimitsClosure J := sorry

end

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (F : C ⥤ D) [PreservesFiniteCoproducts F]

/-- Mapping an additive closure is contained in the additive closure of the mapped property. -/
@[stacks 0FX5]
theorem map_additiveClosure_le (P : ObjectProperty C) :
    P.additiveClosure.map F ≤ (P.map F).additiveClosure := sorry

end

end CategoryTheory.ObjectProperty
