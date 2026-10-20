module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.GradedObject
import Mathlib.Tactic.CrossRefAttribute

/-!
# Graded objects as zero-differential cochain complexes

Every integer-graded object in a category with zero morphisms determines a cochain complex with
zero differential.  The construction is functorial and does not require an additive structure.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.GradedObject

variable {C : Type u} [Category.{v} C] [Limits.HasZeroMorphisms C]

/-- Regard an integer-graded object as a cochain complex with zero differential. -/
@[stacks 0FSF "zero differential on a graded object"]
noncomputable def zeroDifferential (X : GradedObject ℤ C) : CochainComplex C ℤ :=
  CochainComplex.of X (fun _ ↦ 0) (fun _ ↦ sorry)

/-- A morphism of graded objects induces a morphism of their zero-differential complexes. -/
noncomputable def zeroDifferentialMap {X Y : GradedObject ℤ C} (f : X ⟶ Y) :
    zeroDifferential X ⟶ zeroDifferential Y :=
  CochainComplex.ofHom (fun n ↦ f n) (fun _ ↦ sorry)

/-- The zero-differential construction is functorial. -/
@[stacks 0FSF "zero-differential functor on graded objects"]
noncomputable def zeroDifferentialFunctor :
    GradedObject ℤ C ⥤ CochainComplex C ℤ where
  obj := zeroDifferential
  map := zeroDifferentialMap
  map_id := sorry
  map_comp := sorry

/-- The degree-`n` term of the zero-differential complex is the original graded term. -/
@[simp]
theorem zeroDifferential_X (X : GradedObject ℤ C) (n : ℤ) :
    (zeroDifferential X).X n = X n := sorry

/-- Every successor differential in the zero-differential complex is zero. -/
@[simp]
theorem zeroDifferential_d (X : GradedObject ℤ C) (n : ℤ) :
    (zeroDifferential X).d n (n + 1) = 0 := sorry

/-- The degree-`n` component of a zero-differential map is the original graded component. -/
@[simp]
theorem zeroDifferentialMap_f {X Y : GradedObject ℤ C} (f : X ⟶ Y) (n : ℤ) :
    (zeroDifferentialMap f).f n = f n := sorry

/-- The zero-differential functor has the expected object component. -/
@[simp]
theorem zeroDifferentialFunctor_obj (X : GradedObject ℤ C) :
    zeroDifferentialFunctor.obj X = zeroDifferential X := sorry

/-- The zero-differential functor has the expected morphism component. -/
@[simp]
theorem zeroDifferentialFunctor_map {X Y : GradedObject ℤ C} (f : X ⟶ Y) :
    zeroDifferentialFunctor.map f = zeroDifferentialMap f := sorry

end CategoryTheory.GradedObject

end
