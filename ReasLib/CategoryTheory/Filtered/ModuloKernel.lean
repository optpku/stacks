/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Quotient

/-!
# Filtered functors modulo their kernel

A functor is filtered modulo its kernel when quotienting its indexing category by equality after
applying the functor produces a filtered category.  The quotient is the canonical owner; the
elementary common-object and equalization statements are exposed separately for direct use.
-/

@[expose] public section

universe vI uI vC uC vD uD

namespace CategoryTheory.Functor

variable {I : Type uI} [Category.{vI} I]
variable {C : Type uC} [Category.{vC} C]

/-- A functor is filtered modulo its kernel when the quotient by equality of mapped morphisms is
filtered. -/
@[stacks 002V "filtered diagrams modulo their kernel"]
abbrev IsFilteredModuloKernel (M : I ⥤ C) : Prop :=
  IsFiltered (Quotient M.homRel)

/-- Filteredness modulo the kernel is equivalent to nonemptiness, existence of common
successors, and eventual equality after applying the functor. -/
@[stacks 002V "elementary criterion for filteredness modulo a kernel"]
theorem isFilteredModuloKernel_iff (M : I ⥤ C) :
    M.IsFilteredModuloKernel ↔
      Nonempty I ∧
        (∀ x y : I, ∃ z : I, Nonempty (x ⟶ z) ∧ Nonempty (y ⟶ z)) ∧
          ∀ ⦃x y : I⦄ (a b : x ⟶ y),
            ∃ (z : I) (c : y ⟶ z), M.map (a ≫ c) = M.map (b ≫ c) := sorry

namespace IsFilteredModuloKernel

variable {D : Type uD} [Category.{vD} D]

/-- The indexing category of a functor filtered modulo its kernel is nonempty. -/
theorem nonempty (M : I ⥤ C) [M.IsFilteredModuloKernel] : Nonempty I := sorry

/-- Two index objects of a functor filtered modulo its kernel admit a common successor. -/
theorem existsCommonSuccessor (M : I ⥤ C) [M.IsFilteredModuloKernel] (x y : I) :
    ∃ z : I, Nonempty (x ⟶ z) ∧ Nonempty (y ⟶ z) := sorry

/-- Parallel index morphisms become equal after postcomposition and application of a functor
filtered modulo its kernel. -/
theorem existsMapEq (M : I ⥤ C) [M.IsFilteredModuloKernel]
    {x y : I} (a b : x ⟶ y) :
    ∃ (z : I) (c : y ⟶ z), M.map (a ≫ c) = M.map (b ≫ c) := sorry

/-- Construct filteredness modulo the kernel from its three elementary conditions. -/
theorem ofConditions (M : I ⥤ C)
    (h_nonempty : Nonempty I)
    (h_common : ∀ x y : I, ∃ z : I, Nonempty (x ⟶ z) ∧ Nonempty (y ⟶ z))
    (h_equalize : ∀ ⦃x y : I⦄ (a b : x ⟶ y),
      ∃ (z : I) (c : y ⟶ z), M.map (a ≫ c) = M.map (b ≫ c)) :
    M.IsFilteredModuloKernel := sorry

/-- A functor indexed by a filtered category is filtered modulo its kernel. -/
instance ofIsFiltered (M : I ⥤ C) [IsFiltered I] : M.IsFilteredModuloKernel := sorry

/-- For a faithful functor, filteredness modulo its kernel is ordinary filteredness of the
indexing category. -/
@[stacks 002V "faithful specialization of filteredness modulo a kernel"]
theorem iff_of_faithful (M : I ⥤ C) [M.Faithful] :
    M.IsFilteredModuloKernel ↔ IsFiltered I := sorry

/-- Filteredness modulo the kernel is preserved by postcomposition. -/
theorem map (M : I ⥤ C) (F : C ⥤ D) [M.IsFilteredModuloKernel] :
    (M ⋙ F).IsFilteredModuloKernel := sorry

/-- Postcomposition by a faithful functor reflects and preserves filteredness
modulo the kernel. -/
theorem iff_comp_of_faithful (M : I ⥤ C) (F : C ⥤ D) [F.Faithful] :
    (M ⋙ F).IsFilteredModuloKernel ↔ M.IsFilteredModuloKernel := sorry

end IsFilteredModuloKernel

/-- A functor is cofiltered modulo its kernel when its opposite functor is filtered modulo its
kernel. -/
@[stacks 04AZ "cofiltered diagrams modulo their kernel"]
abbrev IsCofilteredModuloKernel (M : I ⥤ C) : Prop :=
  M.op.IsFilteredModuloKernel

/-- Cofilteredness modulo the kernel is equivalent to nonemptiness, existence of common
predecessors, and eventual equality after precomposition and application of the functor. -/
@[stacks 04AZ "elementary criterion for cofilteredness modulo a kernel"]
theorem isCofilteredModuloKernel_iff (M : I ⥤ C) :
    M.IsCofilteredModuloKernel ↔
      Nonempty I ∧
        (∀ x y : I, ∃ z : I, Nonempty (z ⟶ x) ∧ Nonempty (z ⟶ y)) ∧
          ∀ ⦃x y : I⦄ (a b : x ⟶ y),
            ∃ (z : I) (c : z ⟶ x), M.map (c ≫ a) = M.map (c ≫ b) := sorry

namespace IsCofilteredModuloKernel

variable {D : Type uD} [Category.{vD} D]

/-- The indexing category of a functor cofiltered modulo its kernel is nonempty. -/
theorem nonempty (M : I ⥤ C) [M.IsCofilteredModuloKernel] : Nonempty I := sorry

/-- Two index objects of a functor cofiltered modulo its kernel admit a common predecessor. -/
theorem existsCommonPredecessor (M : I ⥤ C) [M.IsCofilteredModuloKernel] (x y : I) :
    ∃ z : I, Nonempty (z ⟶ x) ∧ Nonempty (z ⟶ y) := sorry

/-- Parallel index morphisms become equal after precomposition and application of a functor
cofiltered modulo its kernel. -/
theorem existsMapEq (M : I ⥤ C) [M.IsCofilteredModuloKernel]
    {x y : I} (a b : x ⟶ y) :
    ∃ (z : I) (c : z ⟶ x), M.map (c ≫ a) = M.map (c ≫ b) := sorry

/-- Construct cofilteredness modulo the kernel from its three elementary conditions. -/
theorem ofConditions (M : I ⥤ C)
    (h_nonempty : Nonempty I)
    (h_common : ∀ x y : I, ∃ z : I, Nonempty (z ⟶ x) ∧ Nonempty (z ⟶ y))
    (h_equalize : ∀ ⦃x y : I⦄ (a b : x ⟶ y),
      ∃ (z : I) (c : z ⟶ x), M.map (c ≫ a) = M.map (c ≫ b)) :
    M.IsCofilteredModuloKernel := sorry

/-- A functor indexed by a cofiltered category is cofiltered modulo its kernel. -/
instance ofIsCofiltered (M : I ⥤ C) [IsCofiltered I] :
    M.IsCofilteredModuloKernel := sorry

/-- For a faithful functor, cofilteredness modulo its kernel is ordinary cofilteredness of the
indexing category. -/
@[stacks 04AZ "faithful specialization of cofilteredness modulo a kernel"]
theorem iff_of_faithful (M : I ⥤ C) [M.Faithful] :
    M.IsCofilteredModuloKernel ↔ IsCofiltered I := sorry

/-- Cofilteredness modulo the kernel is preserved by postcomposition. -/
theorem map (M : I ⥤ C) (F : C ⥤ D) [M.IsCofilteredModuloKernel] :
    (M ⋙ F).IsCofilteredModuloKernel := sorry

/-- Postcomposition by a faithful functor reflects and preserves cofilteredness
modulo the kernel. -/
theorem iff_comp_of_faithful (M : I ⥤ C) (F : C ⥤ D) [F.Faithful] :
    (M ⋙ F).IsCofilteredModuloKernel ↔ M.IsCofilteredModuloKernel := sorry

end IsCofilteredModuloKernel

end CategoryTheory.Functor
