/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Epi Covers and Mono Embeddings of Object Properties

This module owns the two dual existence conditions on an object property of an arbitrary
category: every object is covered by an epimorphism from the property, or embeds monomorphically
into an object of the property.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C]

/-- An object property has epi covers when every object receives an epimorphism from an object
satisfying the property. -/
class HasEpiCover (P : ObjectProperty C) : Prop where
  /-- An epimorphic cover of an arbitrary object by an object satisfying the property. -/
  exists_epi (X : C) : ∃ Y : C, P Y ∧ ∃ f : Y ⟶ X, Epi f

/-- An object property has mono embeddings when every object admits a monomorphism into an object
satisfying the property. -/
class HasMonoEmbedding (P : ObjectProperty C) : Prop where
  /-- A monomorphic embedding of an arbitrary object into an object satisfying the property. -/
  exists_mono (X : C) : ∃ Y : C, P Y ∧ ∃ f : X ⟶ Y, Mono f

/-- An object property has epi lifts when every epimorphism onto an object of
the property can be refined by a subobject of its source that also belongs to
the property. -/
@[stacks 0FCL]
class HasEpiLift (P : ObjectProperty C) : Prop where
  /-- Refine an epimorphism onto an object of `P` by a monomorphism from
another object of `P`. -/
  exists_lift {X : C} (Y : P.FullSubcategory) (f : X ⟶ Y.obj) [Epi f] :
    ∃ (X' : P.FullSubcategory) (i : X'.obj ⟶ X), Mono i ∧ Epi (i ≫ f)

namespace top

/-- The maximal object property covers every object by an epimorphism. -/
theorem existsEpi (X : C) :
    ∃ Y : C, (⊤ : ObjectProperty C) Y ∧ ∃ f : Y ⟶ X, Epi f := sorry

/-- The maximal object property has epi covers. -/
instance hasEpiCover : HasEpiCover (⊤ : ObjectProperty C) := sorry

/-- Every object embeds monomorphically into the maximal object property. -/
theorem existsMono (X : C) :
    ∃ Y : C, (⊤ : ObjectProperty C) Y ∧ ∃ f : X ⟶ Y, Mono f := sorry

/-- The maximal object property has mono embeddings. -/
instance hasMonoEmbedding : HasMonoEmbedding (⊤ : ObjectProperty C) := sorry

/-- Epimorphisms onto objects of the maximal property admit tautological epi
lifts. -/
instance hasEpiLift : HasEpiLift (⊤ : ObjectProperty C) := sorry

end top

end CategoryTheory.ObjectProperty
