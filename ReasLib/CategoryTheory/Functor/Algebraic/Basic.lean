/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Categories of algebraic structures

This module packages the categorical properties of a faithful underlying-type functor. Limit
and filtered-colimit sizes are indexed by the universe of the underlying carrier. It also exposes
the small-universe consequences needed by ordinary finite-limit consumers.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe w v u

/-- A category together with a type-valued functor is a type of algebraic structure when the
functor is faithful, preserves limits and filtered colimits, and reflects isomorphisms, while the
category has the corresponding limits and filtered colimits. -/
class IsAlgebraicStructure (C : Type u) [Category.{v} C] (F : C ⥤ Type w) : Prop
    extends F.Faithful, HasLimitsOfSize.{w, w} C, PreservesLimitsOfSize.{w, w} F,
      HasFilteredColimitsOfSize.{w, w} C, PreservesFilteredColimitsOfSize.{w, w} F,
      F.ReflectsIsomorphisms

section

variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w)

/-- The six separate categorical properties canonically produce an algebraic-structure pair.
This construction is explicit so that typeclass search does not have to search backwards through
the six comparatively large categorical classes. -/
theorem isAlgebraicStructureOfProperties [F.Faithful] [HasLimitsOfSize.{w, w} C]
    [PreservesLimitsOfSize.{w, w} F] [HasFilteredColimitsOfSize.{w, w} C]
    [PreservesFilteredColimitsOfSize.{w, w} F] [F.ReflectsIsomorphisms] :
    IsAlgebraicStructure C F := sorry

/-- Being a type of algebraic structure is equivalent to the six constituent categorical
properties. -/
theorem isAlgebraicStructure_iff :
    IsAlgebraicStructure C F ↔
      F.Faithful ∧ HasLimitsOfSize.{w, w} C ∧ PreservesLimitsOfSize.{w, w} F ∧
        HasFilteredColimitsOfSize.{w, w} C ∧ PreservesFilteredColimitsOfSize.{w, w} F ∧
          F.ReflectsIsomorphisms := sorry

set_option synthInstance.checkSynthOrder false in
/-- A category of algebraic structures has finite limits. The conclusion forgets the choice of
underlying-type functor, but typeclass search recovers it from the local algebraic-structure
instance. -/
instance algebraicStructureHasFiniteLimits [IsAlgebraicStructure C F] : HasFiniteLimits C := sorry

/-- The underlying-type functor of a category of algebraic structures preserves finite limits. -/
instance algebraicStructurePreservesFiniteLimits [IsAlgebraicStructure C F] :
    PreservesFiniteLimits F := sorry

/-- In a type of algebraic structures, a morphism is a monomorphism exactly when its underlying
function is injective. -/
theorem mono_iff_underlying_injective [IsAlgebraicStructure C F] {A B : C} (f : A ⟶ B) :
    Mono f ↔ Function.Injective (F.map f) := sorry

/-- In a type of algebraic structures, a morphism with surjective underlying function is an
epimorphism. -/
theorem epi_of_underlying_surjective [IsAlgebraicStructure C F] {A B : C} (f : A ⟶ B)
    (hf : Function.Surjective (F.map f)) : Epi f := sorry

/-- If the range of an underlying morphism lies in the range of an underlying monomorphism, then
the first morphism factors through the canonical subobject represented by the second. Only
pullbacks, their preservation, and reflection of isomorphisms are needed. -/
theorem subobjectFactorsOfRangeSubset
    [HasLimitsOfShape WalkingCospan C] [PreservesLimitsOfShape WalkingCospan F]
    [F.ReflectsIsomorphisms] {A B D : C} (f : A ⟶ B) (g : D ⟶ B) [Mono g]
    (hfg : Set.range (F.map f) ⊆ Set.range (F.map g)) :
    (Subobject.mk g).Factors f := sorry

/-- If an underlying injective morphism contains the range of a second morphism, then the second
morphism factors through it. This is the existential bridge from the canonical
`Subobject.Factors` owner. -/
theorem morphism_factors_through_of_range_subset_of_injective
    [F.Faithful] [HasLimitsOfShape WalkingCospan C]
    [PreservesLimitsOfShape WalkingCospan F] [F.ReflectsIsomorphisms]
    {A B D : C} (f : A ⟶ B) (g : D ⟶ B)
    (hg_injective : Function.Injective (F.map g))
    (hfg : Set.range (F.map f) ⊆ Set.range (F.map g)) :
    ∃ t : A ⟶ D, f = t ≫ g := sorry

namespace IsAlgebraicStructure

/-- The factorization criterion specialized to a type of algebraic structures. This companion is
the universe-stable consumer surface: callers need only the canonical
`IsAlgebraicStructure C F` instance, not separately universe-indexed pullback instances. -/
theorem morphism_factors_through_of_range_subset_of_injective
    [IsAlgebraicStructure C F] {A B D : C} (f : A ⟶ B) (g : D ⟶ B)
    (hg_injective : Function.Injective (F.map g))
    (hfg : Set.range (F.map f) ⊆ Set.range (F.map g)) :
    ∃ t : A ⟶ D, f = t ≫ g := sorry

end IsAlgebraicStructure

/-- If the underlying range of a composite lies in the range of an underlying injection, the
resulting cospan can be completed to a commutative square. -/
theorem exists_commSq_of_composite_range_subset_of_injective
    [IsAlgebraicStructure C F] {A B D E : C}
    (ab : A ⟶ B) (be : B ⟶ E) (de : D ⟶ E)
    (hde_injective : Function.Injective (F.map de))
    (hcomp : Set.range (F.map (ab ≫ be)) ⊆ Set.range (F.map de)) :
    ∃ ad : A ⟶ D, CommSq ab ad be de := sorry

end
