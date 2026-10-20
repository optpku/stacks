/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.Basic
public import ReasLib.Algebra.DirectSum.NonnegGradedAlgebra

/-!
# Morphisms of nonnegatively graded algebras

This file owns degree-preserving morphisms of bundled nonnegatively graded algebras, their
degreewise evaluation API, and the resulting category.  It is independent of divided powers.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped DirectSum

universe u v

namespace NonnegGradedAlgebra

variable {R : Type u} [CommRing R]
variable {A B C D : NonnegGradedAlgebra.{u, v} R}

/-- A degree-preserving homomorphism of nonnegatively graded `R`-algebras. -/
structure Hom (A B : NonnegGradedAlgebra.{u, v} R) where
  /-- The linear map on each homogeneous piece. -/
  map (n : ℕ) : A.piece n →ₗ[R] B.piece n
  /-- The graded unit is preserved. -/
  map_one : map 0 GradedMonoid.GOne.one = GradedMonoid.GOne.one
  /-- Homogeneous multiplication is preserved. -/
  map_mul (n m : ℕ) (x : A.piece n) (y : A.piece m) :
    map (n + m) (GradedMonoid.GMul.mul x y) =
      GradedMonoid.GMul.mul (map n x) (map m y)

namespace Hom

/-- A graded-algebra homomorphism acts degreewise on homogeneous elements. -/
instance : CoeFun (Hom A B) (fun _ ↦ ∀ n : ℕ, A.piece n → B.piece n) where
  coe f n := f.map n

/-- Degreewise evaluation uses the corresponding homogeneous linear map. -/
@[simp] theorem coe_apply (f : Hom A B) (n : ℕ) (x : A.piece n) :
    f n x = f.map n x := sorry

/-- The degreewise identity maps preserve the graded unit. -/
theorem id_map_one (A : NonnegGradedAlgebra.{u, v} R) :
    (LinearMap.id : A.piece 0 →ₗ[R] A.piece 0) GradedMonoid.GOne.one =
      GradedMonoid.GOne.one := sorry

/-- The degreewise identity maps preserve homogeneous multiplication. -/
theorem id_map_mul (A : NonnegGradedAlgebra.{u, v} R) (n m : ℕ)
    (x : A.piece n) (y : A.piece m) :
    (LinearMap.id : A.piece (n + m) →ₗ[R] A.piece (n + m))
        (GradedMonoid.GMul.mul x y) =
      GradedMonoid.GMul.mul
        ((LinearMap.id : A.piece n →ₗ[R] A.piece n) x)
        ((LinearMap.id : A.piece m →ₗ[R] A.piece m) y) := sorry

/-- The identity homomorphism of a nonnegatively graded algebra. -/
def id (A : NonnegGradedAlgebra.{u, v} R) : Hom A A where
  map _ := LinearMap.id
  map_one := id_map_one A
  map_mul := id_map_mul A

/-- Degreewise composition preserves the graded unit. -/
theorem comp_map_one (g : Hom B C) (f : Hom A B) :
    ((g.map 0).comp (f.map 0)) GradedMonoid.GOne.one =
      GradedMonoid.GOne.one := sorry

/-- Degreewise composition preserves homogeneous multiplication. -/
theorem comp_map_mul (g : Hom B C) (f : Hom A B) (n m : ℕ)
    (x : A.piece n) (y : A.piece m) :
    ((g.map (n + m)).comp (f.map (n + m))) (GradedMonoid.GMul.mul x y) =
      GradedMonoid.GMul.mul
        (((g.map n).comp (f.map n)) x) (((g.map m).comp (f.map m)) y) := sorry

/-- Composition of degree-preserving graded-algebra homomorphisms. -/
def comp (g : Hom B C) (f : Hom A B) : Hom A C where
  map n := (g.map n).comp (f.map n)
  map_one := comp_map_one g f
  map_mul := comp_map_mul g f

/-- Graded-algebra homomorphisms are determined by their homogeneous maps. -/
@[ext] theorem ext {f g : Hom A B} (h : ∀ n : ℕ, f.map n = g.map n) : f = g := sorry

/-- The identity graded-algebra homomorphism acts identically in each degree. -/
@[simp] theorem id_apply (A : NonnegGradedAlgebra.{u, v} R) (n : ℕ) (x : A.piece n) :
    id A n x = x := sorry

/-- Composition acts degreewise by ordinary function composition. -/
@[simp] theorem comp_apply (g : Hom B C) (f : Hom A B) (n : ℕ) (x : A.piece n) :
    comp g f n x = g n (f n x) := sorry

/-- Composing with the identity on the source leaves a graded-algebra map unchanged. -/
@[simp] theorem id_comp (f : Hom A B) : comp f (id A) = f := sorry

/-- Composing with the identity on the target leaves a graded-algebra map unchanged. -/
@[simp] theorem comp_id (f : Hom A B) : comp (id B) f = f := sorry

/-- Composition of graded-algebra homomorphisms is associative. -/
theorem assoc (f : Hom A B) (g : Hom B C) (h : Hom C D) :
    comp h (comp g f) = comp (comp h g) f := sorry

/-- The induced linear map on the direct sum of even pieces. -/
def evenMap (f : Hom A B) : A.evenPart →ₗ[R] B.evenPart :=
  DirectSum.toModule R ℕ B.evenPart fun d ↦ (B.evenHom d).comp (f.map (2 * d))

/-- The induced linear map on the direct sum of positive even pieces. -/
def evenPositiveMap (f : Hom A B) : A.evenPositivePart →ₗ[R] B.evenPositivePart :=
  DirectSum.toModule R ℕ B.evenPositivePart fun d ↦
    (B.evenPositiveHom d).comp (f.map (2 * (d + 1)))

/-- The even-part map agrees with the homogeneous maps. -/
theorem evenMap_evenHom (f : Hom A B) (d : ℕ) (x : A.piece (2 * d)) :
    f.evenMap (A.evenHom d x) = B.evenHom d (f.map (2 * d) x) := sorry

/-- The positive-even map agrees with the homogeneous maps. -/
theorem evenPositiveMap_evenPositiveHom (f : Hom A B) (d : ℕ)
    (x : A.piece (2 * (d + 1))) :
    f.evenPositiveMap (A.evenPositiveHom d x) =
      B.evenPositiveHom d (f.map (2 * (d + 1)) x) := sorry

end Hom

end NonnegGradedAlgebra

/-- Nonnegatively graded algebras over a fixed ring and fixed carrier universe form a category. -/
instance {R : Type u} [CommRing R] :
    Category (NonnegGradedAlgebra.{u, v} R) where
  Hom := NonnegGradedAlgebra.Hom
  id := NonnegGradedAlgebra.Hom.id
  comp f g := NonnegGradedAlgebra.Hom.comp g f
  id_comp := NonnegGradedAlgebra.Hom.id_comp
  comp_id := NonnegGradedAlgebra.Hom.comp_id
  assoc := NonnegGradedAlgebra.Hom.assoc

#synth Category (NonnegGradedAlgebra.{0, 0} ℤ)
