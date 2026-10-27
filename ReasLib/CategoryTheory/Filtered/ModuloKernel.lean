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
            ∃ (z : I) (c : y ⟶ z), M.map (a ≫ c) = M.map (b ≫ c) := by
  constructor
  · intro h
    letI : M.IsFilteredModuloKernel := h
    refine ⟨?_, ?_, ?_⟩
    · show Nonempty I
      obtain ⟨⟨i⟩⟩ := (IsFiltered.nonempty : Nonempty (Quotient M.homRel))
      exact ⟨i⟩
    · intro x y
      obtain ⟨⟨z⟩, ⟨a⟩, ⟨b⟩, _⟩ := IsFilteredOrEmpty.cocone_objs
        ((Quotient.functor M.homRel).obj x) ((Quotient.functor M.homRel).obj y)
      exact ⟨z, ⟨a⟩, ⟨b⟩⟩
    · intro x y a b
      obtain ⟨⟨z⟩, ⟨c⟩, hc⟩ := IsFilteredOrEmpty.cocone_maps
        ((Quotient.functor M.homRel).map a) ((Quotient.functor M.homRel).map b)
      exact ⟨z, c, (Quotient.functor_map_eq_iff M.homRel (a ≫ c) (b ≫ c)).mp hc⟩
  · rintro ⟨⟨i⟩, h_common, h_equalize⟩
    refine
      { nonempty := ⟨⟨i⟩⟩
        cocone_objs := ?_
        cocone_maps := ?_ }
    · rintro ⟨x⟩ ⟨y⟩
      obtain ⟨z, ⟨a⟩, ⟨b⟩⟩ := h_common x y
      exact ⟨⟨z⟩, (Quotient.functor M.homRel).map a,
        (Quotient.functor M.homRel).map b, trivial⟩
    · rintro ⟨x⟩ ⟨y⟩ ⟨a⟩ ⟨b⟩
      obtain ⟨z, c, hc⟩ := h_equalize a b
      exact ⟨⟨z⟩, (Quotient.functor M.homRel).map c, Quotient.sound M.homRel hc⟩

namespace IsFilteredModuloKernel

variable {D : Type uD} [Category.{vD} D]

/-- The indexing category of a functor filtered modulo its kernel is nonempty. -/
theorem nonempty (M : I ⥤ C) [M.IsFilteredModuloKernel] : Nonempty I := by
  exact ((isFilteredModuloKernel_iff M).mp inferInstance).1

/-- Two index objects of a functor filtered modulo its kernel admit a common successor. -/
theorem existsCommonSuccessor (M : I ⥤ C) [M.IsFilteredModuloKernel] (x y : I) :
    ∃ z : I, Nonempty (x ⟶ z) ∧ Nonempty (y ⟶ z) := by
  exact ((isFilteredModuloKernel_iff M).mp inferInstance).2.1 x y

/-- Parallel index morphisms become equal after postcomposition and application of a functor
filtered modulo its kernel. -/
theorem existsMapEq (M : I ⥤ C) [M.IsFilteredModuloKernel]
    {x y : I} (a b : x ⟶ y) :
    ∃ (z : I) (c : y ⟶ z), M.map (a ≫ c) = M.map (b ≫ c) := by
  exact ((isFilteredModuloKernel_iff M).mp inferInstance).2.2 a b

/-- Construct filteredness modulo the kernel from its three elementary conditions. -/
theorem ofConditions (M : I ⥤ C)
    (h_nonempty : Nonempty I)
    (h_common : ∀ x y : I, ∃ z : I, Nonempty (x ⟶ z) ∧ Nonempty (y ⟶ z))
    (h_equalize : ∀ ⦃x y : I⦄ (a b : x ⟶ y),
      ∃ (z : I) (c : y ⟶ z), M.map (a ≫ c) = M.map (b ≫ c)) :
    M.IsFilteredModuloKernel := by
  exact (isFilteredModuloKernel_iff M).mpr ⟨h_nonempty, h_common, h_equalize⟩

/-- A functor indexed by a filtered category is filtered modulo its kernel. -/
instance ofIsFiltered (M : I ⥤ C) [IsFiltered I] : M.IsFilteredModuloKernel := by
  refine ofConditions M IsFiltered.nonempty ?_ ?_
  · intro x y
    obtain ⟨z, a, b, _⟩ := IsFilteredOrEmpty.cocone_objs x y
    exact ⟨z, ⟨a⟩, ⟨b⟩⟩
  · intro x y a b
    obtain ⟨z, c, hc⟩ := IsFilteredOrEmpty.cocone_maps a b
    exact ⟨z, c, congrArg M.map hc⟩

/-- For a faithful functor, filteredness modulo its kernel is ordinary filteredness of the
indexing category. -/
@[stacks 002V "faithful specialization of filteredness modulo a kernel"]
theorem iff_of_faithful (M : I ⥤ C) [M.Faithful] :
    M.IsFilteredModuloKernel ↔ IsFiltered I := by
  constructor
  · intro h
    letI : M.IsFilteredModuloKernel := h
    refine
      { nonempty := nonempty M
        cocone_objs := ?_
        cocone_maps := ?_ }
    · intro x y
      obtain ⟨z, ⟨a⟩, ⟨b⟩⟩ := existsCommonSuccessor M x y
      exact ⟨z, a, b, trivial⟩
    · intro x y a b
      obtain ⟨z, c, hc⟩ := existsMapEq M a b
      exact ⟨z, c, M.map_injective hc⟩
  · intro h
    letI : IsFiltered I := h
    exact ofIsFiltered M

/-- Filteredness modulo the kernel is preserved by postcomposition. -/
theorem map (M : I ⥤ C) (F : C ⥤ D) [M.IsFilteredModuloKernel] :
    (M ⋙ F).IsFilteredModuloKernel := by
  refine ofConditions (M ⋙ F) (nonempty M) (existsCommonSuccessor M) ?_
  intro x y a b
  obtain ⟨z, c, hc⟩ := existsMapEq M a b
  exact ⟨z, c, congrArg F.map hc⟩

/-- Postcomposition by a faithful functor reflects and preserves filteredness
modulo the kernel. -/
theorem iff_comp_of_faithful (M : I ⥤ C) (F : C ⥤ D) [F.Faithful] :
    (M ⋙ F).IsFilteredModuloKernel ↔ M.IsFilteredModuloKernel := by
  constructor
  · intro h
    letI : (M ⋙ F).IsFilteredModuloKernel := h
    refine ofConditions M (nonempty (M ⋙ F)) (existsCommonSuccessor (M ⋙ F)) ?_
    intro x y a b
    obtain ⟨z, c, hc⟩ := existsMapEq (M ⋙ F) a b
    exact ⟨z, c, F.map_injective hc⟩
  · intro h
    letI : M.IsFilteredModuloKernel := h
    exact map M F

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
            ∃ (z : I) (c : z ⟶ x), M.map (c ≫ a) = M.map (c ≫ b) := by
  constructor
  · intro h
    obtain ⟨h_nonempty, h_common, h_equalize⟩ := (isFilteredModuloKernel_iff M.op).mp h
    refine ⟨h_nonempty.map Opposite.unop, ?_, ?_⟩
    · intro x y
      obtain ⟨z, ⟨a⟩, ⟨b⟩⟩ := h_common (Opposite.op x) (Opposite.op y)
      exact ⟨z.unop, ⟨a.unop⟩, ⟨b.unop⟩⟩
    · intro x y a b
      obtain ⟨z, c, hc⟩ := h_equalize a.op b.op
      refine ⟨z.unop, c.unop, ?_⟩
      change (M.map (c.unop ≫ a)).op = (M.map (c.unop ≫ b)).op at hc
      exact Quiver.Hom.op_inj hc
  · rintro ⟨h_nonempty, h_common, h_equalize⟩
    apply (isFilteredModuloKernel_iff M.op).mpr
    refine ⟨h_nonempty.map Opposite.op, ?_, ?_⟩
    · intro x y
      obtain ⟨z, ⟨a⟩, ⟨b⟩⟩ := h_common x.unop y.unop
      exact ⟨Opposite.op z, ⟨a.op⟩, ⟨b.op⟩⟩
    · intro x y a b
      obtain ⟨z, c, hc⟩ := h_equalize a.unop b.unop
      refine ⟨Opposite.op z, c.op, ?_⟩
      change (M.map (c ≫ a.unop)).op = (M.map (c ≫ b.unop)).op
      exact congrArg Quiver.Hom.op hc

namespace IsCofilteredModuloKernel

variable {D : Type uD} [Category.{vD} D]

/-- The indexing category of a functor cofiltered modulo its kernel is nonempty. -/
theorem nonempty (M : I ⥤ C) [M.IsCofilteredModuloKernel] : Nonempty I := by
  exact ((isCofilteredModuloKernel_iff M).mp inferInstance).1

/-- Two index objects of a functor cofiltered modulo its kernel admit a common predecessor. -/
theorem existsCommonPredecessor (M : I ⥤ C) [M.IsCofilteredModuloKernel] (x y : I) :
    ∃ z : I, Nonempty (z ⟶ x) ∧ Nonempty (z ⟶ y) := by
  exact ((isCofilteredModuloKernel_iff M).mp inferInstance).2.1 x y

/-- Parallel index morphisms become equal after precomposition and application of a functor
cofiltered modulo its kernel. -/
theorem existsMapEq (M : I ⥤ C) [M.IsCofilteredModuloKernel]
    {x y : I} (a b : x ⟶ y) :
    ∃ (z : I) (c : z ⟶ x), M.map (c ≫ a) = M.map (c ≫ b) := by
  exact ((isCofilteredModuloKernel_iff M).mp inferInstance).2.2 a b

/-- Construct cofilteredness modulo the kernel from its three elementary conditions. -/
theorem ofConditions (M : I ⥤ C)
    (h_nonempty : Nonempty I)
    (h_common : ∀ x y : I, ∃ z : I, Nonempty (z ⟶ x) ∧ Nonempty (z ⟶ y))
    (h_equalize : ∀ ⦃x y : I⦄ (a b : x ⟶ y),
      ∃ (z : I) (c : z ⟶ x), M.map (c ≫ a) = M.map (c ≫ b)) :
    M.IsCofilteredModuloKernel := by
  exact (isCofilteredModuloKernel_iff M).mpr ⟨h_nonempty, h_common, h_equalize⟩

/-- A functor indexed by a cofiltered category is cofiltered modulo its kernel. -/
instance ofIsCofiltered (M : I ⥤ C) [IsCofiltered I] :
    M.IsCofilteredModuloKernel := by
  exact IsFilteredModuloKernel.ofIsFiltered M.op

/-- For a faithful functor, cofilteredness modulo its kernel is ordinary cofilteredness of the
indexing category. -/
@[stacks 04AZ "faithful specialization of cofilteredness modulo a kernel"]
theorem iff_of_faithful (M : I ⥤ C) [M.Faithful] :
    M.IsCofilteredModuloKernel ↔ IsCofiltered I := by
  exact (IsFilteredModuloKernel.iff_of_faithful M.op).trans
    (isFiltered_op_iff_isCofiltered (C := I))

/-- Cofilteredness modulo the kernel is preserved by postcomposition. -/
theorem map (M : I ⥤ C) (F : C ⥤ D) [M.IsCofilteredModuloKernel] :
    (M ⋙ F).IsCofilteredModuloKernel := by
  exact IsFilteredModuloKernel.map M.op F.op

/-- Postcomposition by a faithful functor reflects and preserves cofilteredness
modulo the kernel. -/
theorem iff_comp_of_faithful (M : I ⥤ C) (F : C ⥤ D) [F.Faithful] :
    (M ⋙ F).IsCofilteredModuloKernel ↔ M.IsCofilteredModuloKernel := by
  exact IsFilteredModuloKernel.iff_comp_of_faithful M.op F.op

end IsCofilteredModuloKernel

end CategoryTheory.Functor
