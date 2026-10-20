/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra

/-!
# Semilinear morphisms of chain differential graded algebras

This file owns morphisms of chain DGAs whose source and target have different scalar rings.
The scalar map is explicit, and the morphism records degreewise semilinearity together with
compatibility with the differential, unit, and homogeneous multiplication.
-/

@[expose] public section

noncomputable section

universe uR uS uT uA uB uC

namespace ChainDGAlgebra

variable {R : Type uR} {S : Type uS} {T : Type uT}
variable [CommRing R] [CommRing S] [CommRing T]

/-- A chain-DGA morphism semilinear along a specified homomorphism of scalar rings. -/
@[stacks 09PQ "semilinear morphism of chain differential graded algebras"]
structure SemilinearHom (sigma : R →+* S) (A : ChainDGAlgebra.{uR, uA} R)
    (B : ChainDGAlgebra.{uS, uB} S) where
  /-- The semilinear map on each homogeneous component. -/
  map (n : ℤ) : A.X n →ₛₗ[sigma] B.X n
  /-- The homogeneous maps commute with the chain differentials. -/
  map_d (n : ℤ) (x : A.X n) :
    map (n - 1) (A.d n x) = B.d n (map n x)
  /-- The degree-zero unit is preserved. -/
  map_one : map 0 A.one = B.one
  /-- Homogeneous multiplication is preserved. -/
  map_mul (n m : ℤ) (x : A.X n) (y : A.X m) :
    map (n + m) (A.mul n m x y) = B.mul n m (map n x) (map m y)

namespace SemilinearHom

variable {sigma : R →+* S} {tau : S →+* T}
variable {A : ChainDGAlgebra.{uR, uA} R}
variable {B : ChainDGAlgebra.{uS, uB} S}
variable {C : ChainDGAlgebra.{uT, uC} T}

/-- A semilinear chain-DGA morphism acts degreewise on homogeneous elements. -/
instance instCoeFun : CoeFun (SemilinearHom sigma A B)
    (fun _ ↦ ∀ n : ℤ, A.X n → B.X n) where
  coe f := fun n x ↦ f.map n x

/-- Degreewise evaluation uses the corresponding semilinear map. -/
@[simp]
theorem coe_apply (f : SemilinearHom sigma A B) (n : ℤ) (x : A.X n) :
    f n x = f.map n x := sorry

/-- A semilinear chain-DGA morphism preserves addition in each degree. -/
@[simp]
theorem map_add (f : SemilinearHom sigma A B) (n : ℤ) (x y : A.X n) :
    f n (x + y) = f n x + f n y := sorry

/-- A semilinear chain-DGA morphism carries source scalars through its scalar map. -/
@[simp]
theorem map_smul (f : SemilinearHom sigma A B) (n : ℤ) (r : R) (x : A.X n) :
    f n (r • x) = sigma r • f n x := sorry

/-- A semilinear chain-DGA morphism commutes with the differential. -/
@[simp]
theorem map_d_apply (f : SemilinearHom sigma A B) (n : ℤ) (x : A.X n) :
    f (n - 1) (A.d n x) = B.d n (f n x) := sorry

/-- A semilinear chain-DGA morphism preserves the unit. -/
@[simp]
theorem map_one_apply (f : SemilinearHom sigma A B) : f 0 A.one = B.one := sorry

/-- A semilinear chain-DGA morphism preserves homogeneous multiplication. -/
@[simp]
theorem map_mul_apply (f : SemilinearHom sigma A B) (n m : ℤ)
    (x : A.X n) (y : A.X m) :
    f (n + m) (A.mul n m x y) = B.mul n m (f n x) (f m y) := sorry

/-- The identity function on one homogeneous component, regarded as semilinear along the
identity ring homomorphism. -/
def idMap (A : ChainDGAlgebra.{uR, uA} R) (n : ℤ) :
    A.X n →ₛₗ[RingHom.id R] A.X n :=
  LinearMap.id

/-- The degreewise identity maps commute with the differential. -/
theorem id_map_d (A : ChainDGAlgebra.{uR, uA} R) (n : ℤ) (x : A.X n) :
    idMap A (n - 1) (A.d n x) = A.d n (idMap A n x) := sorry

/-- The degreewise identity maps preserve the unit. -/
theorem id_map_one (A : ChainDGAlgebra.{uR, uA} R) : idMap A 0 A.one = A.one := sorry

/-- The degreewise identity maps preserve homogeneous multiplication. -/
theorem id_map_mul (A : ChainDGAlgebra.{uR, uA} R) (n m : ℤ)
    (x : A.X n) (y : A.X m) :
    idMap A (n + m) (A.mul n m x y) =
      A.mul n m (idMap A n x) (idMap A m y) := sorry

/-- The identity semilinear morphism of a chain DGA. -/
def id (A : ChainDGAlgebra.{uR, uA} R) :
    SemilinearHom (RingHom.id R) A A where
  map := idMap A
  map_d := id_map_d A
  map_one := id_map_one A
  map_mul := id_map_mul A

/-- The identity semilinear morphism acts pointwise as the identity. -/
@[simp]
theorem id_apply (A : ChainDGAlgebra.{uR, uA} R) (n : ℤ) (x : A.X n) :
    id A n x = x := sorry

/-- Pointwise composition of homogeneous semilinear maps preserves addition. -/
theorem compMap_add (g : SemilinearHom tau B C) (f : SemilinearHom sigma A B)
    (n : ℤ) (x y : A.X n) :
    g n (f n (x + y)) = g n (f n x) + g n (f n y) := sorry

/-- Pointwise composition is semilinear along the composite scalar map. -/
theorem compMap_smul (g : SemilinearHom tau B C) (f : SemilinearHom sigma A B)
    (n : ℤ) (r : R) (x : A.X n) :
    g n (f n (r • x)) = (tau.comp sigma) r • g n (f n x) := sorry

/-- The pointwise composite of homogeneous semilinear maps. -/
def compMap (g : SemilinearHom tau B C) (f : SemilinearHom sigma A B) (n : ℤ) :
    A.X n →ₛₗ[tau.comp sigma] C.X n where
  toFun := fun x ↦ g n (f n x)
  map_add' := compMap_add g f n
  map_smul' := compMap_smul g f n

/-- Composite homogeneous maps commute with the differential. -/
theorem comp_map_d (g : SemilinearHom tau B C) (f : SemilinearHom sigma A B)
    (n : ℤ) (x : A.X n) :
    compMap g f (n - 1) (A.d n x) = C.d n (compMap g f n x) := sorry

/-- Composite homogeneous maps preserve the unit. -/
theorem comp_map_one (g : SemilinearHom tau B C) (f : SemilinearHom sigma A B) :
    compMap g f 0 A.one = C.one := sorry

/-- Composite homogeneous maps preserve multiplication. -/
theorem comp_map_mul (g : SemilinearHom tau B C) (f : SemilinearHom sigma A B)
    (n m : ℤ) (x : A.X n) (y : A.X m) :
    compMap g f (n + m) (A.mul n m x y) =
      C.mul n m (compMap g f n x) (compMap g f m y) := sorry

/-- Composition of semilinear chain-DGA morphisms. -/
def comp (g : SemilinearHom tau B C) (f : SemilinearHom sigma A B) :
    SemilinearHom (tau.comp sigma) A C where
  map := compMap g f
  map_d := comp_map_d g f
  map_one := comp_map_one g f
  map_mul := comp_map_mul g f

/-- Composition of semilinear chain-DGA morphisms acts pointwise. -/
@[simp]
theorem comp_apply (g : SemilinearHom tau B C) (f : SemilinearHom sigma A B)
    (n : ℤ) (x : A.X n) : comp g f n x = g n (f n x) := sorry

/-- Semilinear chain-DGA morphisms are determined by their homogeneous maps. -/
@[ext]
theorem ext {f g : SemilinearHom sigma A B}
    (h : ∀ (n : ℤ) (x : A.X n), f n x = g n x) : f = g := sorry

/-- A semilinear chain-DGA morphism is degreewise surjective. -/
def Surjective (f : SemilinearHom sigma A B) : Prop :=
  ∀ n : ℤ, Function.Surjective (f.map n)

/-- A semilinear chain-DGA morphism is degreewise injective. -/
def Injective (f : SemilinearHom sigma A B) : Prop :=
  ∀ n : ℤ, Function.Injective (f.map n)

/-- A semilinear chain-DGA morphism is degreewise bijective. -/
def Bijective (f : SemilinearHom sigma A B) : Prop :=
  f.Injective ∧ f.Surjective

end SemilinearHom

end ChainDGAlgebra
