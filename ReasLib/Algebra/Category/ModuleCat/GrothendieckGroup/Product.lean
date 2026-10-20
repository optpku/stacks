/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Product.Finite
public import ReasLib.Algebra.Category.ModuleCat.Product.FiniteProjective
public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Basic
public import ReasLib.CategoryTheory.Abelian.GrothendieckGroup.Property.Functor
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Grothendieck Groups of Product Rings

Modules over a product ring split into their two idempotent factors.  This file presents the
resulting maps on the projective and finite-module Grothendieck groups.  The low-level factor
construction and its finite/projective closures live in the neutral `ModuleCat.Product` layers;
this file keeps only the Grothendieck-group maps and equivalences in the separate `Projective` and
`Finite` namespaces.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace CategoryTheory.ModuleCat.K0.Product

namespace Projective

variable (R : Type u) (S : Type v) [Ring R] [Ring S]

/-- The pair of projective Grothendieck classes obtained from the two idempotent factors. -/
@[stacks 00JH "projective K0 factor classes"]
def factorClass (M : ModuleCat.FiniteProjective.{max u v, w} (R × S)) :
    projective.{u, w} R × projective.{v, w} S :=
  ( projectiveOf.{u, w} R (ModuleCat.Product.FiniteProjective.left R S M)
  , projectiveOf.{v, w} S (ModuleCat.Product.FiniteProjective.right R S M) )

/-- The projective Grothendieck homomorphism induced by the left idempotent factor. -/
@[stacks 00JH "projective K0 left factor map"]
def leftFactorMap : projective.{max u v, w} (R × S) →+ projective.{u, w} R :=
  ObjectProperty.GrothendieckGroup.mapExact (ModuleCat.Product.leftExactFunctor R S)
    (fun M hM ↦ ModuleCat.Product.FiniteProjective.left_mem R S M hM)

/-- The projective Grothendieck homomorphism induced by the right idempotent factor. -/
@[stacks 00JH "projective K0 right factor map"]
def rightFactorMap : projective.{max u v, w} (R × S) →+ projective.{v, w} S :=
  ObjectProperty.GrothendieckGroup.mapExact (ModuleCat.Product.rightExactFunctor R S)
    (fun M hM ↦ ModuleCat.Product.FiniteProjective.right_mem R S M hM)

/-- The homomorphism on projective Grothendieck groups induced by idempotent factorization. -/
@[stacks 00JH "projective K0 factor map"]
def factorMap : projective.{max u v, w} (R × S) →+
    projective.{u, w} R × projective.{v, w} S :=
  (leftFactorMap.{u, v, w} R S).prod (rightFactorMap.{u, v, w} R S)

/-- The left projective factor map evaluates on a generator by taking its left factor. -/
@[simp]
theorem leftFactorMap_of (M : ModuleCat.FiniteProjective.{max u v, w} (R × S)) :
    leftFactorMap.{u, v, w} R S (projectiveOf.{max u v, w} (R × S) M) =
      projectiveOf.{u, w} R (ModuleCat.Product.FiniteProjective.left R S M) := sorry

/-- The right projective factor map evaluates on a generator by taking its right factor. -/
@[simp]
theorem rightFactorMap_of (M : ModuleCat.FiniteProjective.{max u v, w} (R × S)) :
    rightFactorMap.{u, v, w} R S (projectiveOf.{max u v, w} (R × S) M) =
      projectiveOf.{v, w} S (ModuleCat.Product.FiniteProjective.right R S M) := sorry

/-- The projective factor map evaluates on a generator by taking its two idempotent factors. -/
@[simp]
theorem factorMap_of (M : ModuleCat.FiniteProjective.{max u v, w} (R × S)) :
    factorMap.{u, v, w} R S (projectiveOf.{max u v, w} (R × S) M) =
      factorClass.{u, v, w} R S M := sorry

/-- The projective Grothendieck homomorphism induced by the first product projection. -/
@[stacks 00JH "projective K0 left embedding map"]
def leftEmbedMap : projective.{u, w} R →+ projective.{max u v, w} (R × S) :=
  ObjectProperty.GrothendieckGroup.mapExact (ModuleCat.Product.leftEmbedExact R S)
    (fun M hM ↦ ModuleCat.Product.FiniteProjective.leftEmbed_mem R S M hM)

/-- The projective Grothendieck homomorphism induced by the second product projection. -/
@[stacks 00JH "projective K0 right embedding map"]
def rightEmbedMap : projective.{v, w} S →+ projective.{max u v, w} (R × S) :=
  ObjectProperty.GrothendieckGroup.mapExact (ModuleCat.Product.rightEmbedExact R S)
    (fun M hM ↦ ModuleCat.Product.FiniteProjective.rightEmbed_mem R S M hM)

/-- The left projective embedding map evaluates on a generator by restriction along the first
projection. -/
@[simp]
theorem leftEmbedMap_of (M : ModuleCat.FiniteProjective.{u, w} R) :
    leftEmbedMap.{u, v, w} R S (projectiveOf.{u, w} R M) =
      projectiveOf.{max u v, w} (R × S)
        ((ModuleCat.Product.FiniteProjective.leftEmbed R S).obj M) := sorry

/-- The right projective embedding map evaluates on a generator by restriction along the second
projection. -/
@[simp]
theorem rightEmbedMap_of (M : ModuleCat.FiniteProjective.{v, w} S) :
    rightEmbedMap.{u, v, w} R S (projectiveOf.{v, w} S M) =
      projectiveOf.{max u v, w} (R × S)
        ((ModuleCat.Product.FiniteProjective.rightEmbed R S).obj M) := sorry

/-- The candidate inverse to the projective factor map, obtained by adding the two embeddings. -/
@[stacks 00JH "projective K0 factor map inverse"]
def inverse : projective.{u, w} R × projective.{v, w} S →+
    projective.{max u v, w} (R × S) :=
  (leftEmbedMap.{u, v, w} R S).coprod (rightEmbedMap.{u, v, w} R S)

/-- The inverse projective factor map adds the images of the two components. -/
@[simp]
theorem inverse_apply (x : projective.{u, w} R × projective.{v, w} S) :
    inverse.{u, v, w} R S x =
      leftEmbedMap.{u, v, w} R S x.1 + rightEmbedMap.{u, v, w} R S x.2 := sorry

/-- Factoring after the two projective embeddings is the identity. -/
theorem factorMap_comp_inverse :
    (factorMap.{u, v, w} R S).comp (inverse.{u, v, w} R S) =
      AddMonoidHom.id (projective.{u, w} R × projective.{v, w} S) := sorry

/-- Re-embedding the two idempotent factors is the identity on projective Grothendieck groups. -/
theorem inverse_comp_factorMap :
    (inverse.{u, v, w} R S).comp (factorMap.{u, v, w} R S) =
      AddMonoidHom.id (projective.{max u v, w} (R × S)) := sorry

/-- Factoring after the inverse projective factor map acts as the identity on elements. -/
@[simp]
theorem factorMap_inverse_apply (x : projective.{u, w} R × projective.{v, w} S) :
    factorMap.{u, v, w} R S (inverse.{u, v, w} R S x) = x := sorry

/-- Applying the inverse after the projective factor map acts as the identity on elements. -/
@[simp]
theorem inverse_factorMap_apply (x : projective.{max u v, w} (R × S)) :
    inverse.{u, v, w} R S (factorMap.{u, v, w} R S x) = x := sorry

/-- Stacks 00JH (1): the canonical product decomposition of projective Grothendieck groups. -/
@[stacks 00JH]
def equiv : projective.{max u v, w} (R × S) ≃+
    projective.{u, w} R × projective.{v, w} S where
  toFun := factorMap.{u, v, w} R S
  invFun := inverse.{u, v, w} R S
  left_inv := DFunLike.congr_fun (inverse_comp_factorMap.{u, v, w} R S)
  right_inv := DFunLike.congr_fun (factorMap_comp_inverse.{u, v, w} R S)
  map_add' := (factorMap.{u, v, w} R S).map_add

/-- The projective product equivalence sends a generator to the classes of its two factors. -/
@[simp, stacks 00JH]
theorem equiv_apply_of (M : ModuleCat.FiniteProjective.{max u v, w} (R × S)) :
    equiv.{u, v, w} R S (projectiveOf.{max u v, w} (R × S) M) =
      factorClass.{u, v, w} R S M := sorry

end Projective

namespace Finite

variable (R : Type u) (S : Type v) [Ring R] [Ring S]

/-- The pair of finite-module Grothendieck classes obtained from the two idempotent factors. -/
@[stacks 00JH "finite K0 factor classes"]
def factorClass (M : FGModuleCat.{w} (R × S)) : finite.{u, w} R × finite.{v, w} S :=
  ( finiteOf.{u, w} R (ModuleCat.Product.Finite.left R S M)
  , finiteOf.{v, w} S (ModuleCat.Product.Finite.right R S M) )

/-- The finite-module Grothendieck homomorphism induced by the left idempotent factor. -/
@[stacks 00JH "finite K0 left factor map"]
def leftFactorMap : finite.{max u v, w} (R × S) →+ finite.{u, w} R :=
  ObjectProperty.GrothendieckGroup.mapExact (ModuleCat.Product.leftExactFunctor R S)
    (fun M hM ↦ ModuleCat.Product.Finite.left_mem R S M hM)

/-- The finite-module Grothendieck homomorphism induced by the right idempotent factor. -/
@[stacks 00JH "finite K0 right factor map"]
def rightFactorMap : finite.{max u v, w} (R × S) →+ finite.{v, w} S :=
  ObjectProperty.GrothendieckGroup.mapExact (ModuleCat.Product.rightExactFunctor R S)
    (fun M hM ↦ ModuleCat.Product.Finite.right_mem R S M hM)

/-- The homomorphism on finite-module Grothendieck groups induced by idempotent factorization. -/
@[stacks 00JH "finite-module K0 factor map"]
def factorMap : finite.{max u v, w} (R × S) →+ finite.{u, w} R × finite.{v, w} S :=
  (leftFactorMap.{u, v, w} R S).prod (rightFactorMap.{u, v, w} R S)

/-- The left finite-module factor map evaluates on a generator by taking its left factor. -/
@[simp]
theorem leftFactorMap_of (M : FGModuleCat.{w} (R × S)) :
    leftFactorMap.{u, v, w} R S (finiteOf.{max u v, w} (R × S) M) =
      finiteOf.{u, w} R (ModuleCat.Product.Finite.left R S M) := sorry

/-- The right finite-module factor map evaluates on a generator by taking its right factor. -/
@[simp]
theorem rightFactorMap_of (M : FGModuleCat.{w} (R × S)) :
    rightFactorMap.{u, v, w} R S (finiteOf.{max u v, w} (R × S) M) =
      finiteOf.{v, w} S (ModuleCat.Product.Finite.right R S M) := sorry

/-- The finite-module factor map evaluates on a generator by taking its two idempotent factors. -/
@[simp]
theorem factorMap_of (M : FGModuleCat.{w} (R × S)) :
    factorMap.{u, v, w} R S (finiteOf.{max u v, w} (R × S) M) =
      factorClass.{u, v, w} R S M := sorry

/-- The finite-module Grothendieck homomorphism induced by the first product projection. -/
@[stacks 00JH "finite K0 left embedding map"]
def leftEmbedMap : finite.{u, w} R →+ finite.{max u v, w} (R × S) :=
  ObjectProperty.GrothendieckGroup.mapExact (ModuleCat.Product.leftEmbedExact R S)
    (fun M hM ↦ ModuleCat.Product.Finite.leftEmbed_mem R S M hM)

/-- The finite-module Grothendieck homomorphism induced by the second product projection. -/
@[stacks 00JH "finite K0 right embedding map"]
def rightEmbedMap : finite.{v, w} S →+ finite.{max u v, w} (R × S) :=
  ObjectProperty.GrothendieckGroup.mapExact (ModuleCat.Product.rightEmbedExact R S)
    (fun M hM ↦ ModuleCat.Product.Finite.rightEmbed_mem R S M hM)

/-- The left finite-module embedding map evaluates on a generator by restriction along the first
projection. -/
@[simp]
theorem leftEmbedMap_of (M : FGModuleCat.{w} R) :
    leftEmbedMap.{u, v, w} R S (finiteOf.{u, w} R M) =
      finiteOf.{max u v, w} (R × S) ((ModuleCat.Product.Finite.leftEmbed R S).obj M) := sorry

/-- The right finite-module embedding map evaluates on a generator by restriction along the second
projection. -/
@[simp]
theorem rightEmbedMap_of (M : FGModuleCat.{w} S) :
    rightEmbedMap.{u, v, w} R S (finiteOf.{v, w} S M) =
      finiteOf.{max u v, w} (R × S) ((ModuleCat.Product.Finite.rightEmbed R S).obj M) := sorry

/-- The candidate inverse to the finite-module factor map, obtained by adding the two embeddings.
-/
@[stacks 00JH "finite K0 factor map inverse"]
def inverse : finite.{u, w} R × finite.{v, w} S →+ finite.{max u v, w} (R × S) :=
  (leftEmbedMap.{u, v, w} R S).coprod (rightEmbedMap.{u, v, w} R S)

/-- The inverse finite factor map adds the images of the two components. -/
@[simp]
theorem inverse_apply (x : finite.{u, w} R × finite.{v, w} S) :
    inverse.{u, v, w} R S x =
      leftEmbedMap.{u, v, w} R S x.1 + rightEmbedMap.{u, v, w} R S x.2 := sorry

/-- Factoring after the two finite-module embeddings is the identity. -/
theorem factorMap_comp_inverse :
    (factorMap.{u, v, w} R S).comp (inverse.{u, v, w} R S) =
      AddMonoidHom.id (finite.{u, w} R × finite.{v, w} S) := sorry

/-- Re-embedding the two idempotent factors is the identity on finite-module Grothendieck groups.
-/
theorem inverse_comp_factorMap :
    (inverse.{u, v, w} R S).comp (factorMap.{u, v, w} R S) =
      AddMonoidHom.id (finite.{max u v, w} (R × S)) := sorry

/-- Factoring after the inverse finite factor map acts as the identity on elements. -/
@[simp]
theorem factorMap_inverse_apply (x : finite.{u, w} R × finite.{v, w} S) :
    factorMap.{u, v, w} R S (inverse.{u, v, w} R S x) = x := sorry

/-- Applying the inverse after the finite factor map acts as the identity on elements. -/
@[simp]
theorem inverse_factorMap_apply (x : finite.{max u v, w} (R × S)) :
    inverse.{u, v, w} R S (factorMap.{u, v, w} R S x) = x := sorry

/-- Stacks 00JH (2): the canonical product decomposition of finite-module Grothendieck groups. -/
@[stacks 00JH]
def equiv : finite.{max u v, w} (R × S) ≃+ finite.{u, w} R × finite.{v, w} S where
  toFun := factorMap.{u, v, w} R S
  invFun := inverse.{u, v, w} R S
  left_inv := DFunLike.congr_fun (inverse_comp_factorMap.{u, v, w} R S)
  right_inv := DFunLike.congr_fun (factorMap_comp_inverse.{u, v, w} R S)
  map_add' := (factorMap.{u, v, w} R S).map_add

/-- The finite product equivalence sends a generator to the classes of its two factors. -/
@[simp, stacks 00JH]
theorem equiv_apply_of (M : FGModuleCat.{w} (R × S)) :
    equiv.{u, v, w} R S (finiteOf.{max u v, w} (R × S) M) =
      factorClass.{u, v, w} R S M := sorry

end Finite

variable (R : Type u) (S : Type v) [Ring R] [Ring S]

/-- The projective-to-finite comparison commutes with factorization over a product ring. -/
@[stacks 00JH "projective-to-finite product compatibility"]
theorem projectiveToFinite_factorMap :
    ((projectiveToFinite.{u, w} R).prodMap (projectiveToFinite.{v, w} S)).comp
        (Projective.factorMap R S) =
      (Finite.factorMap R S).comp (projectiveToFinite.{max u v, w} (R × S)) := sorry

end CategoryTheory.ModuleCat.K0.Product

end
