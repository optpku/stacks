module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# Successive objects

A successive object is an integer-indexed family with successor maps, without a
square-zero condition. A square-zero family determines a cochain complex.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ZeroObject

noncomputable section

universe u v u₂ v₂

namespace CategoryTheory

/-- An integer-indexed family of objects with successor maps, without a square-zero law. -/
structure Successive (C : Type u) [Category.{v} C] where
  /-- The object in degree `n`. -/
  X : ℤ → C
  /-- The successor map out of degree `n`. -/
  d : ∀ n, X n ⟶ X (n + 1)

namespace Successive

variable {C : Type u} [Category.{v} C]

/-- The successive object with the specified terms and successor maps. -/
def ofMaps (X : ℤ → C) (d : ∀ n, X n ⟶ X (n + 1)) : Successive C where
  X := X
  d := d

/-- The successive object whose terms and successor maps are zero. -/
def zero [HasZeroObject C] [HasZeroMorphisms C] : Successive C :=
  ofMaps (fun _ ↦ 0) (fun _ ↦ 0)

/-- A degreewise morphism of successive objects commuting with their successor maps. -/
structure Hom (G F : Successive C) where
  /-- The component in degree `n`. -/
  f : ∀ n, G.X n ⟶ F.X n
  /-- Each successor square commutes. -/
  comm : ∀ n, G.d n ≫ f (n + 1) = f n ≫ F.d n

namespace Hom

/-- The morphism of successive objects with specified components and commuting squares. -/
def ofMaps {G F : Successive C} (f : ∀ n, G.X n ⟶ F.X n)
    (comm : ∀ n, G.d n ≫ f (n + 1) = f n ≫ F.d n) : Hom G F where
  f := f
  comm := comm

end Hom

/-- The successive object obtained by applying a functor to every term and successor map. -/
def map {D : Type u₂} [Category.{v₂} D] (G : Successive C) (F : C ⥤ D) : Successive D where
  X n := F.obj (G.X n)
  d n := F.map (G.d n)

variable [HasZeroMorphisms C]

/-- The cochain complex associated to a successive object whose successor maps square to zero. -/
def toCochainComplex (G : Successive C) (h : ∀ n, G.d n ≫ G.d (n + 1) = 0) :
    CochainComplex C ℤ :=
  CochainComplex.of G.X G.d h

/-- The terms of the associated cochain complex are the original family. -/
theorem toCochainComplex_X (G : Successive C) (h : ∀ n, G.d n ≫ G.d (n + 1) = 0) :
    (G.toCochainComplex h).X = G.X := sorry

/-- The successor differentials of the associated cochain complex are the original maps. -/
theorem toCochainComplex_d (G : Successive C) (h : ∀ n, G.d n ≫ G.d (n + 1) = 0) (n : ℤ) :
    (G.toCochainComplex h).d n (n + 1) = G.d n := sorry

variable [HasZeroObject C]

/-- A successive object is strictly bounded above by `N` if all terms in degrees `> N` vanish. -/
def IsStrictlyLE (G : Successive C) (N : ℤ) : Prop :=
  ∀ n, N < n → IsZero (G.X n)

/-- A strict upper bound is equivalent to vanishing of all terms in larger degrees. -/
theorem isStrictlyLE_iff (G : Successive C) (N : ℤ) :
    G.IsStrictlyLE N ↔ ∀ n, N < n → IsZero (G.X n) := sorry

/-- Existence of a strict upper bound is equivalent to eventual termwise vanishing. -/
theorem exists_bound_iff (G : Successive C) :
    (∃ N, G.IsStrictlyLE N) ↔ ∃ N, ∀ n, N < n → IsZero (G.X n) := sorry

end Successive

end CategoryTheory
