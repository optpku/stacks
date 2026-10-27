/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.ChainGradedAlgebra

/-!
# Morphisms of chain-graded algebras

This file defines degree-preserving algebra homomorphisms between externally
presented chain-graded algebras, their category, and the forgetful functor to
graded `ModuleCat` objects.
-/

@[expose] public section

universe u v

open CategoryTheory

variable {R : Type u} [CommRing R]

/-- A degree-preserving homomorphism of chain-graded algebras. -/
@[stacks 09PR "infrastructure: homomorphisms of chain-graded algebras"]
structure ChainGradedAlgebra.Hom (A B : ChainGradedAlgebra.{u, v} R) where
  /-- The degreewise linear map. -/
  map (i : ℤ) : A.X i →ₗ[R] B.X i
  /-- The degreewise map preserves the unit. -/
  map_one : map 0 A.one = B.one
  /-- The degreewise map preserves multiplication of homogeneous elements. -/
  map_mul (i j : ℤ) (a : A.X i) (b : A.X j) :
    map (i + j) (A.mul i j a b) = B.mul i j (map i a) (map j b)

namespace ChainGradedAlgebra.Hom

variable {A B C D : ChainGradedAlgebra.{u, v} R}

/-- A graded-algebra homomorphism acts on each homogeneous component. -/
instance instCoeFun : CoeFun (Hom A B) (fun _ ↦ ∀ i : ℤ, A.X i → B.X i) where
  coe f := fun i x ↦ f.map i x

/-- Evaluation of a graded-algebra homomorphism is evaluation of its degreewise map. -/
@[simp]
theorem coe_apply (f : Hom A B) (i : ℤ) (x : A.X i) :
    f i x = f.map i x := rfl

/-- A graded-algebra homomorphism preserves the unit. -/
@[simp]
theorem map_one_apply (f : Hom A B) : f 0 A.one = B.one := by
  exact f.map_one

/-- A graded-algebra homomorphism preserves multiplication of homogeneous elements. -/
@[simp]
theorem map_mul_apply (f : Hom A B) (i j : ℤ) (a : A.X i) (b : A.X j) :
    f (i + j) (A.mul i j a b) = B.mul i j (f i a) (f j b) := by
  exact f.map_mul i j a b

/-- The degreewise linear family underlying the identity homomorphism. -/
def idMap (A : ChainGradedAlgebra.{u, v} R) :
    ∀ i : ℤ, A.X i →ₗ[R] A.X i :=
  fun _ ↦ LinearMap.id

/-- The identity family preserves the unit. -/
theorem idMap_one (A : ChainGradedAlgebra.{u, v} R) :
    idMap A 0 A.one = A.one := rfl

/-- The identity family preserves homogeneous multiplication. -/
theorem idMap_mul (A : ChainGradedAlgebra.{u, v} R) (i j : ℤ)
    (a : A.X i) (b : A.X j) :
    idMap A (i + j) (A.mul i j a b) =
      A.mul i j (idMap A i a) (idMap A j b) := rfl

/-- The identity homomorphism of a chain-graded algebra. -/
def id (A : ChainGradedAlgebra.{u, v} R) : Hom A A where
  map := idMap A
  map_one := idMap_one A
  map_mul := idMap_mul A

/-- The degreewise family underlying a composite homomorphism. -/
def compMap (g : Hom B C) (f : Hom A B) :
    ∀ i : ℤ, A.X i →ₗ[R] C.X i :=
  fun i ↦ (g.map i).comp (f.map i)

/-- The composite degreewise family preserves the unit. -/
theorem compMap_one (g : Hom B C) (f : Hom A B) :
    compMap g f 0 A.one = C.one := by
  change g.map 0 (f.map 0 A.one) = C.one
  rw [f.map_one, g.map_one]

/-- The composite degreewise family preserves homogeneous multiplication. -/
theorem compMap_mul (g : Hom B C) (f : Hom A B) (i j : ℤ)
    (a : A.X i) (b : A.X j) :
    compMap g f (i + j) (A.mul i j a b) =
      C.mul i j (compMap g f i a) (compMap g f j b) := by
  change g.map (i + j) (f.map (i + j) (A.mul i j a b)) =
    C.mul i j (g.map i (f.map i a)) (g.map j (f.map j b))
  rw [f.map_mul, g.map_mul]

/-- Composition of degree-preserving graded-algebra homomorphisms. -/
def comp (g : Hom B C) (f : Hom A B) : Hom A C where
  map := compMap g f
  map_one := compMap_one g f
  map_mul := compMap_mul g f

/-- The degreewise map of the identity homomorphism is the identity linear map. -/
@[simp]
theorem id_map (A : ChainGradedAlgebra.{u, v} R) (i : ℤ) :
    (id A).map i = LinearMap.id := rfl

/-- The degreewise map of a composite is the composite of the degreewise maps. -/
@[simp]
theorem comp_map (g : Hom B C) (f : Hom A B) (i : ℤ) :
    (comp g f).map i = (g.map i).comp (f.map i) := rfl

/-- The identity homomorphism acts as the identity on homogeneous elements. -/
@[simp]
theorem id_apply (A : ChainGradedAlgebra.{u, v} R) (i : ℤ) (x : A.X i) :
    id A i x = x := rfl

/-- Composition acts by pointwise function composition. -/
@[simp]
theorem comp_apply (g : Hom B C) (f : Hom A B) (i : ℤ) (x : A.X i) :
    comp g f i x = g i (f i x) := rfl

/-- Homomorphisms are determined by their degreewise linear maps. -/
theorem ext_map {f g : Hom A B} (h : ∀ i : ℤ, f.map i = g.map i) :
    f = g := by
  cases f
  cases g
  cases funext h
  rfl

/-- Homomorphisms are determined by their values on homogeneous elements. -/
@[ext]
theorem ext {f g : Hom A B}
    (h : ∀ i : ℤ, ∀ x : A.X i, f i x = g i x) : f = g := by
  apply ext_map
  intro i
  exact LinearMap.ext (h i)

/-- Left composition with an identity homomorphism is neutral. -/
@[simp]
theorem id_comp (f : Hom A B) : comp f (id A) = f := by
  apply ext
  intro i x
  rfl

/-- Right composition with an identity homomorphism is neutral. -/
@[simp]
theorem comp_id (f : Hom A B) : comp (id B) f = f := by
  apply ext
  intro i x
  rfl

/-- Composition of chain-graded algebra homomorphisms is associative. -/
theorem assoc (f : Hom A B) (g : Hom B C) (h : Hom C D) :
    comp h (comp g f) = comp (comp h g) f := by
  apply ext
  intro i x
  rfl

/-- The morphism of graded objects underlying a chain-graded algebra homomorphism. -/
def toGradedMap (f : Hom A B) : A.toGradedObject ⟶ B.toGradedObject :=
  fun i ↦ ModuleCat.ofHom (f.map i)

/-- The underlying graded-object map is the corresponding degreewise module morphism. -/
@[simp]
theorem toGradedMap_apply (f : Hom A B) (i : ℤ) :
    f.toGradedMap i = ModuleCat.ofHom (f.map i) := rfl

/-- The identity homomorphism induces the identity morphism of graded objects. -/
theorem toGradedMap_id (A : ChainGradedAlgebra.{u, v} R) :
    (id A).toGradedMap = 𝟙 A.toGradedObject := rfl

/-- A composite homomorphism induces the composite morphism of graded objects. -/
theorem toGradedMap_comp (g : Hom B C) (f : Hom A B) :
    (comp g f).toGradedMap = f.toGradedMap ≫ g.toGradedMap := rfl

end ChainGradedAlgebra.Hom

namespace ChainGradedAlgebra

/-- Chain-graded algebras and degree-preserving algebra homomorphisms form a category. -/
instance instCategory : Category (ChainGradedAlgebra.{u, v} R) where
  Hom A B := Hom A B
  id A := Hom.id A
  comp f g := Hom.comp g f
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

/-- A categorical arrow of chain-graded algebras acts degreewise. -/
instance instCategoryCoeFun {A B : ChainGradedAlgebra.{u, v} R} :
    CoeFun (A ⟶ B) (fun _ ↦ ∀ i : ℤ, A.X i → B.X i) where
  coe f := fun i x ↦ ((f : Hom A B).map i) x

/-- The categorical identity is the explicit identity homomorphism. -/
@[simp]
theorem category_id (A : ChainGradedAlgebra.{u, v} R) :
    (𝟙 A : A ⟶ A) = (Hom.id A : A ⟶ A) := rfl

/-- Categorical composition is explicit composition of graded-algebra homomorphisms. -/
@[simp]
theorem category_comp {A B C : ChainGradedAlgebra.{u, v} R}
    (f : A ⟶ B) (g : B ⟶ C) :
    f ≫ g = (Hom.comp (g : Hom B C) (f : Hom A B) : A ⟶ C) := rfl

/-- Forget a chain-graded algebra to its graded object of modules. -/
@[stacks 09PR "infrastructure: the forgetful functor for chain-graded algebras"]
def forget : ChainGradedAlgebra.{u, v} R ⥤ GradedObject ℤ (ModuleCat.{v} R) where
  obj A := A.toGradedObject
  map f := Hom.toGradedMap (f : Hom _ _)
  map_id A := Hom.toGradedMap_id A
  map_comp f g := Hom.toGradedMap_comp (g : Hom _ _) (f : Hom _ _)

/-- The forgetful functor sends an algebra to its underlying graded object. -/
@[simp]
theorem forget_obj (A : ChainGradedAlgebra.{u, v} R) :
    (forget (R := R)).obj A = A.toGradedObject := rfl

/-- Evaluation after forgetting returns the corresponding homogeneous component. -/
@[simp]
theorem forget_obj_apply (A : ChainGradedAlgebra.{u, v} R) (i : ℤ) :
    (forget (R := R)).obj A i = A.X i := rfl

/-- The forgetful functor acts on morphisms degreewise. -/
@[simp]
theorem forget_map_apply {A B : ChainGradedAlgebra.{u, v} R}
    (f : A ⟶ B) (i : ℤ) :
    (forget (R := R)).map f i =
      ModuleCat.ofHom ((f : Hom A B).map i) := rfl

/-- The linear map underlying the forgotten degree-`i` morphism is `f.map i`. -/
@[simp]
theorem forget_map_hom {A B : ChainGradedAlgebra.{u, v} R}
    (f : A ⟶ B) (i : ℤ) :
    ((forget (R := R)).map f i).hom = (f : Hom A B).map i := rfl

end ChainGradedAlgebra
