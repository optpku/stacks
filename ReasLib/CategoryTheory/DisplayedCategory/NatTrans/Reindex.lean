/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DisplayedCategory.NatTrans

/-!
# Reindex calculus for displayed natural transformations

The core natural-transformation leaf owns equality transport and compatibility with vertical
composition.  This leaf supplies the cancellation and injectivity interface used by downstream
normalization arguments.
-/

@[expose] public section

namespace CategoryTheory.DisplayedNatTrans

universe v u v' u'

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
variable {D : DisplayedCategory C} {E : DisplayedCategory C'}
variable {F G : C ⥤ C'} {Φ : DisplayedFunctor D E F} {Ψ : DisplayedFunctor D E G}

/-- Reindexing a displayed transformation forward and then backward recovers it. -/
@[simp]
theorem reindex_symm_apply {α β : F ⟶ G} (h : α = β)
    (η : DisplayedNatTrans Φ Ψ α) :
    reindex h.symm (reindex h η) = η := sorry

/-- Reindexing a displayed transformation backward and then forward recovers it. -/
@[simp]
theorem reindex_apply_symm {α β : F ⟶ G} (h : α = β)
    (η : DisplayedNatTrans Φ Ψ β) :
    reindex h (reindex h.symm η) = η := sorry

/-- Reindexing along a base-transformation equality is injective. -/
theorem reindex_injective {α β : F ⟶ G} (h : α = β) :
    Function.Injective
      (reindex h : DisplayedNatTrans Φ Ψ α → DisplayedNatTrans Φ Ψ β) := sorry

/-- Equality after a common displayed-transformation reindexing is equivalent to equality before
it. -/
@[simp]
theorem reindex_eq_iff {α β : F ⟶ G} (h : α = β)
    (η θ : DisplayedNatTrans Φ Ψ α) :
    reindex h η = reindex h θ ↔ η = θ := sorry

end CategoryTheory.DisplayedNatTrans
