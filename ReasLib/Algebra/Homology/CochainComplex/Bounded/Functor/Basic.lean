/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Functors on bounded cochain complexes

This file restricts the termwise action of a zero-morphism-preserving functor to
bounded-above and bounded cochain complexes.  It owns the preservation statements,
the restricted functors, and their inclusion-level computation API.
-/

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.Cochain

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]
  [HasZeroMorphisms C] [HasZeroMorphisms D]

namespace Minus

/-- A zero-morphism-preserving functor carries the bounded-above cochain object property
into the bounded-above cochain object property. -/
@[stacks 014X "preservation of bounded-above cochain complexes"]
theorem mapsTo (F : C ⥤ D) [F.PreservesZeroMorphisms] :
    CochainComplex.minus C ≤
      (CochainComplex.minus D).inverseImage
        (F.mapHomologicalComplex (up ℤ)) := sorry

/-- A zero-morphism-preserving functor sends bounded-above cochain complexes to
bounded-above cochain complexes. -/
theorem obj_mem (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : CochainComplex.Minus C) :
    CochainComplex.minus D ((F.mapHomologicalComplex (up ℤ)).obj K.obj) := sorry

/-- The functor on bounded-above cochain complexes induced by a
zero-morphism-preserving functor. -/
@[stacks 014X "bounded-above cochain functor"]
def map (F : C ⥤ D) [F.PreservesZeroMorphisms] :
    CochainComplex.Minus C ⥤ CochainComplex.Minus D :=
  ObjectProperty.FullSubcategory.restrict
    (F.mapHomologicalComplex (up ℤ)) (mapsTo F)

/-- Forgetting bounded-above structure after `Functor.Cochain.Minus.map` recovers the
ambient termwise functor. -/
def compInclusionIso (F : C ⥤ D) [F.PreservesZeroMorphisms] :
    map F ⋙ CochainComplex.Minus.ι D ≅
      CochainComplex.Minus.ι C ⋙ F.mapHomologicalComplex (up ℤ) :=
  ObjectProperty.FullSubcategory.restrict.compιIso
    (F.mapHomologicalComplex (up ℤ)) (mapsTo F)

/-- Objectwise computation for the bounded-above cochain functor. -/
@[simp]
theorem obj_obj (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : CochainComplex.Minus C) :
    ((map F).obj K).obj = (F.mapHomologicalComplex (up ℤ)).obj K.obj := sorry

/-- Morphismwise computation for the bounded-above cochain functor. -/
@[simp]
theorem map_hom (F : C ⥤ D) [F.PreservesZeroMorphisms]
    {K L : CochainComplex.Minus C} (f : K ⟶ L) :
    ((map F).map f).hom = (F.mapHomologicalComplex (up ℤ)).map f.hom := sorry

/-- The forward inclusion comparison for the bounded-above cochain functor is
componentwise the identity. -/
@[simp]
theorem compInclusionIso_hom_app (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : CochainComplex.Minus C) :
    (compInclusionIso F).hom.app K =
      𝟙 ((F.mapHomologicalComplex (up ℤ)).obj K.obj) := sorry

/-- The inverse inclusion comparison for the bounded-above cochain functor is
componentwise the identity. -/
@[simp]
theorem compInclusionIso_inv_app (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : CochainComplex.Minus C) :
    (compInclusionIso F).inv.app K =
      𝟙 ((F.mapHomologicalComplex (up ℤ)).obj K.obj) := sorry

end Minus

namespace Bounded

/-- A zero-morphism-preserving functor carries the bounded cochain object property into
the bounded cochain object property. -/
@[stacks 014X "preservation of bounded cochain complexes"]
theorem mapsTo (F : C ⥤ D) [F.PreservesZeroMorphisms] :
    CochainComplex.bounded C ≤
      (CochainComplex.bounded D).inverseImage
        (F.mapHomologicalComplex (up ℤ)) := sorry

/-- A zero-morphism-preserving functor sends bounded cochain complexes to bounded cochain
complexes. -/
theorem obj_mem (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : CochainComplex.Bounded C) :
    CochainComplex.bounded D ((F.mapHomologicalComplex (up ℤ)).obj K.obj) := sorry

/-- The functor on bounded cochain complexes induced by a zero-morphism-preserving functor. -/
@[stacks 014X "bounded cochain functor"]
def map (F : C ⥤ D) [F.PreservesZeroMorphisms] :
    CochainComplex.Bounded C ⥤ CochainComplex.Bounded D :=
  ObjectProperty.FullSubcategory.restrict
    (F.mapHomologicalComplex (up ℤ)) (mapsTo F)

/-- Forgetting bounded structure after `Functor.Cochain.Bounded.map` recovers the ambient
termwise functor. -/
def compInclusionIso (F : C ⥤ D) [F.PreservesZeroMorphisms] :
    map F ⋙ CochainComplex.Bounded.ι D ≅
      CochainComplex.Bounded.ι C ⋙ F.mapHomologicalComplex (up ℤ) :=
  ObjectProperty.FullSubcategory.restrict.compιIso
    (F.mapHomologicalComplex (up ℤ)) (mapsTo F)

/-- Objectwise computation for the bounded cochain functor. -/
@[simp]
theorem obj_obj (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : CochainComplex.Bounded C) :
    ((map F).obj K).obj = (F.mapHomologicalComplex (up ℤ)).obj K.obj := sorry

/-- Morphismwise computation for the bounded cochain functor. -/
@[simp]
theorem map_hom (F : C ⥤ D) [F.PreservesZeroMorphisms]
    {K L : CochainComplex.Bounded C} (f : K ⟶ L) :
    ((map F).map f).hom = (F.mapHomologicalComplex (up ℤ)).map f.hom := sorry

/-- The forward inclusion comparison for the bounded cochain functor is componentwise the
identity. -/
@[simp]
theorem compInclusionIso_hom_app (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : CochainComplex.Bounded C) :
    (compInclusionIso F).hom.app K =
      𝟙 ((F.mapHomologicalComplex (up ℤ)).obj K.obj) := sorry

/-- The inverse inclusion comparison for the bounded cochain functor is componentwise the
identity. -/
@[simp]
theorem compInclusionIso_inv_app (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : CochainComplex.Bounded C) :
    (compInclusionIso F).inv.app K =
      𝟙 ((F.mapHomologicalComplex (up ℤ)).obj K.obj) := sorry

end Bounded

end CategoryTheory.Functor.Cochain
