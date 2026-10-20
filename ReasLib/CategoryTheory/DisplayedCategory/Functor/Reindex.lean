/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DisplayedCategory.Functor

/-!
# Reindex calculus for displayed functors

This leaf completes the equality-transport API for displayed functors.  It keeps cancellation and
compatibility with composition out of the core construction file while making propositionally
equal presentations of base functors interchangeable downstream.
-/

@[expose] public section

namespace CategoryTheory.DisplayedFunctor

universe v u v' u' v'' u''

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
variable {D : DisplayedCategory C} {E : DisplayedCategory C'}

/-- Reindexing a displayed functor forward and then backward recovers it. -/
@[simp]
theorem reindex_symm_apply {F G : C ⥤ C'} (h : F = G)
    (Φ : DisplayedFunctor D E F) :
    reindex h.symm (reindex h Φ) = Φ := sorry

/-- Reindexing a displayed functor backward and then forward recovers it. -/
@[simp]
theorem reindex_apply_symm {F G : C ⥤ C'} (h : F = G)
    (Φ : DisplayedFunctor D E G) :
    reindex h (reindex h.symm Φ) = Φ := sorry

/-- Reindexing along a base-functor equality is injective. -/
theorem reindex_injective {F G : C ⥤ C'} (h : F = G) :
    Function.Injective
      (reindex h : DisplayedFunctor D E F → DisplayedFunctor D E G) := sorry

/-- Equality after a common displayed-functor reindexing is equivalent to equality before it. -/
@[simp]
theorem reindex_eq_iff {F G : C ⥤ C'} (h : F = G)
    (Φ Ψ : DisplayedFunctor D E F) :
    reindex h Φ = reindex h Ψ ↔ Φ = Ψ := sorry

/-- Reindexing both factors of a displayed composite agrees with reindexing the composite base
functor. -/
@[simp]
theorem comp_reindex
    {C'' : Type u''} [Category.{v''} C''] {E' : DisplayedCategory C''}
    {F F' : C ⥤ C'} {G G' : C' ⥤ C''}
    (h : F = F') (k : G = G')
    (Φ : DisplayedFunctor D E F) (Ψ : DisplayedFunctor E E' G) :
    reindex
        (congrArg₂ (fun (L : C ⥤ C') (R : C' ⥤ C'') => L ⋙ R) h k)
        (comp Φ Ψ) =
      comp (reindex h Φ) (reindex k Ψ) := sorry

end CategoryTheory.DisplayedFunctor
