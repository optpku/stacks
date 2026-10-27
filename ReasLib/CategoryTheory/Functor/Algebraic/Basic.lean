/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
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
    IsAlgebraicStructure C F where
  toFaithful := inferInstance
  toHasLimitsOfSize := inferInstance
  toPreservesLimitsOfSize := inferInstance
  toHasFilteredColimitsOfSize := inferInstance
  toPreservesFilteredColimitsOfSize := inferInstance
  toReflectsIsomorphisms := inferInstance

/-- Being a type of algebraic structure is equivalent to the six constituent categorical
properties. -/
theorem isAlgebraicStructure_iff :
    IsAlgebraicStructure C F ↔
      F.Faithful ∧ HasLimitsOfSize.{w, w} C ∧ PreservesLimitsOfSize.{w, w} F ∧
        HasFilteredColimitsOfSize.{w, w} C ∧ PreservesFilteredColimitsOfSize.{w, w} F ∧
          F.ReflectsIsomorphisms := by
  constructor
  · intro h
    letI := h
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
  · rintro ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩
    letI := h₁
    letI := h₂
    letI := h₃
    letI := h₄
    letI := h₅
    letI := h₆
    exact isAlgebraicStructureOfProperties F

set_option synthInstance.checkSynthOrder false in
/-- A category of algebraic structures has finite limits. The conclusion forgets the choice of
underlying-type functor, but typeclass search recovers it from the local algebraic-structure
instance. -/
instance algebraicStructureHasFiniteLimits [IsAlgebraicStructure C F] : HasFiniteLimits C :=
  hasFiniteLimits_of_hasLimitsOfSize.{w, w} C

/-- The underlying-type functor of a category of algebraic structures preserves finite limits. -/
instance algebraicStructurePreservesFiniteLimits [IsAlgebraicStructure C F] :
    PreservesFiniteLimits F :=
  PreservesLimitsOfSize.preservesFiniteLimits.{w, w} F

/-- In a type of algebraic structures, a morphism is a monomorphism exactly when its underlying
function is injective. -/
theorem mono_iff_underlying_injective [IsAlgebraicStructure C F] {A B : C} (f : A ⟶ B) :
    Mono f ↔ Function.Injective (F.map f) :=
  (F.mono_map_iff_mono f).symm.trans (CategoryTheory.mono_iff_injective (F.map f))

/-- In a type of algebraic structures, a morphism with surjective underlying function is an
epimorphism. -/
theorem epi_of_underlying_surjective [IsAlgebraicStructure C F] {A B : C} (f : A ⟶ B)
    (hf : Function.Surjective (F.map f)) : Epi f :=
  F.epi_of_epi_map ((CategoryTheory.epi_iff_surjective (F.map f)).2 hf)

/-- If the range of an underlying morphism lies in the range of an underlying monomorphism, then
the first morphism factors through the canonical subobject represented by the second. Only
pullbacks, their preservation, and reflection of isomorphisms are needed. -/
theorem subobjectFactorsOfRangeSubset
    [HasLimitsOfShape WalkingCospan C] [PreservesLimitsOfShape WalkingCospan F]
    [F.ReflectsIsomorphisms] {A B D : C} (f : A ⟶ B) (g : D ⟶ B) [Mono g]
    (hfg : Set.range (F.map f) ⊆ Set.range (F.map g)) :
    (Subobject.mk g).Factors f := by
  let e := PullbackCone.IsLimit.equivPullbackObj
    (isLimitOfHasPullbackOfPreservesLimit F f g)
  have hsurj : Function.Surjective (F.map (pullback.fst f g)) := by
    intro a
    obtain ⟨d, hd⟩ := hfg ⟨a, rfl⟩
    refine ⟨e.symm ⟨⟨a, d⟩, hd.symm⟩, ?_⟩
    exact PullbackCone.IsLimit.equivPullbackObj_symm_apply_fst
      (isLimitOfHasPullbackOfPreservesLimit F f g) ⟨⟨a, d⟩, hd.symm⟩
  haveI : IsIso (F.map (pullback.fst f g)) :=
    (CategoryTheory.isIso_iff_bijective _).2
      ⟨(CategoryTheory.mono_iff_injective _).1 inferInstance, hsurj⟩
  haveI : IsIso (pullback.fst f g) := isIso_of_reflects_iso _ F
  change ∃ t : A ⟶ D, t ≫ g = f
  refine ⟨inv (pullback.fst f g) ≫ pullback.snd f g, ?_⟩
  rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]

/-- If an underlying injective morphism contains the range of a second morphism, then the second
morphism factors through it. This is the existential bridge from the canonical
`Subobject.Factors` owner. -/
theorem morphism_factors_through_of_range_subset_of_injective
    [F.Faithful] [HasLimitsOfShape WalkingCospan C]
    [PreservesLimitsOfShape WalkingCospan F] [F.ReflectsIsomorphisms]
    {A B D : C} (f : A ⟶ B) (g : D ⟶ B)
    (hg_injective : Function.Injective (F.map g))
    (hfg : Set.range (F.map f) ⊆ Set.range (F.map g)) :
    ∃ t : A ⟶ D, f = t ≫ g := by
  haveI : Mono (F.map g) := (CategoryTheory.mono_iff_injective _).2 hg_injective
  haveI : Mono g := F.mono_of_mono_map inferInstance
  obtain ⟨t, ht⟩ := (Subobject.mk_factors_iff g f).1
    (subobjectFactorsOfRangeSubset F f g hfg)
  exact ⟨t, ht.symm⟩

namespace IsAlgebraicStructure

/-- The factorization criterion specialized to a type of algebraic structures. This companion is
the universe-stable consumer surface: callers need only the canonical
`IsAlgebraicStructure C F` instance, not separately universe-indexed pullback instances. -/
theorem morphism_factors_through_of_range_subset_of_injective
    [IsAlgebraicStructure C F] {A B D : C} (f : A ⟶ B) (g : D ⟶ B)
    (hg_injective : Function.Injective (F.map g))
    (hfg : Set.range (F.map f) ⊆ Set.range (F.map g)) :
    ∃ t : A ⟶ D, f = t ≫ g := by
  letI := algebraicStructureHasFiniteLimits F
  exact _root_.morphism_factors_through_of_range_subset_of_injective F f g hg_injective hfg

end IsAlgebraicStructure

/-- If the underlying range of a composite lies in the range of an underlying injection, the
resulting cospan can be completed to a commutative square. -/
theorem exists_commSq_of_composite_range_subset_of_injective
    [IsAlgebraicStructure C F] {A B D E : C}
    (ab : A ⟶ B) (be : B ⟶ E) (de : D ⟶ E)
    (hde_injective : Function.Injective (F.map de))
    (hcomp : Set.range (F.map (ab ≫ be)) ⊆ Set.range (F.map de)) :
    ∃ ad : A ⟶ D, CommSq ab ad be de := by
  obtain ⟨ad, had⟩ :=
    IsAlgebraicStructure.morphism_factors_through_of_range_subset_of_injective
      F (ab ≫ be) de hde_injective hcomp
  exact ⟨ad, ⟨had⟩⟩

end
