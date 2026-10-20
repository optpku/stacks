/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra

/-!
# Morphisms of Cochain Differential Graded Algebras

This leaf owns concrete cochain-DGA morphisms and their category structure.
It is deliberately independent of module and enrichment constructions.
-/

@[expose] public section

universe u v w x

open CategoryTheory

variable {R : Type u} [CommRing R]

/-- Definition 22.3.2: a homomorphism of cochain differential graded algebras.  The source and
target carrier universes are independent. -/
@[stacks 061X]
structure CochainDGAlgebra.Hom
    (A : CochainDGAlgebra.{u, v} R) (B : CochainDGAlgebra.{u, w} R) where
  /-- The degreewise linear maps. -/
  map (n : ℤ) : A.X n →ₗ[R] B.X n
  /-- The degreewise maps commute with the differentials. -/
  comm_d (i j : ℤ) (h : (ComplexShape.up ℤ).Rel i j) :
    (B.toCochainComplex.d i j).hom.comp (map i) =
      (map j).comp (A.toCochainComplex.d i j).hom
  /-- The unit is preserved. -/
  map_one : map 0 A.one = B.one
  /-- Homogeneous multiplication is preserved. -/
  map_mul (n m : ℤ) (a : A.X n) (b : A.X m) :
    map (n + m) (A.mul n m a b) = B.mul n m (map n a) (map m b)

namespace CochainDGAlgebra.Hom

variable {A : CochainDGAlgebra.{u, v} R} {B : CochainDGAlgebra.{u, w} R}
  {C : CochainDGAlgebra.{u, x} R}

/-- A same-universe cochain-DGA homomorphism has an underlying cochain map. -/
def toCochainMap {A B : CochainDGAlgebra.{u, v} R} (f : Hom A B) :
    A.toCochainComplex ⟶ B.toCochainComplex where
  f n := ModuleCat.ofHom (f.map n)
  comm' := sorry

/-- The component of the underlying cochain map is the degreewise linear map. -/
@[simp] theorem toCochainMap_f {A B : CochainDGAlgebra.{u, v} R}
    (f : Hom A B) (n : ℤ) :
    f.toCochainMap.f n = ModuleCat.ofHom (f.map n) := sorry

/-- The identity cochain-DGA homomorphism. -/
def id (A : CochainDGAlgebra.{u, v} R) : Hom A A where
  map _ := LinearMap.id
  comm_d := sorry
  map_one := sorry
  map_mul := sorry

/-- Composition of cochain-DGA homomorphisms. -/
def comp (g : Hom B C) (f : Hom A B) : Hom A C where
  map n := (g.map n).comp (f.map n)
  comm_d := sorry
  map_one := sorry
  map_mul := sorry

/-- The underlying cochain map of the identity homomorphism. -/
@[simp] theorem id_toCochainMap (A : CochainDGAlgebra.{u, v} R) :
    (id A).toCochainMap = 𝟙 A.toCochainComplex := sorry

/-- The underlying cochain map of a composite homomorphism. -/
@[simp] theorem comp_toCochainMap {A B C : CochainDGAlgebra.{u, v} R}
    (g : Hom B C) (f : Hom A B) :
    (comp g f).toCochainMap = f.toCochainMap ≫ g.toCochainMap := sorry

/-- Cochain-DGA homomorphisms are determined by their underlying cochain maps. -/
theorem ext_toCochainMap {A B : CochainDGAlgebra.{u, v} R} {f g : Hom A B}
    (h : f.toCochainMap = g.toCochainMap) : f = g := sorry

/-- Cochain-DGA homomorphisms in arbitrary carrier universes are determined degreewise. -/
theorem ext_map {f g : Hom A B} (h : ∀ n : ℤ, f.map n = g.map n) : f = g := sorry

end CochainDGAlgebra.Hom

namespace CochainDGAlgebra

/-- Cochain differential graded algebras form a category. -/
instance instCategory : Category (CochainDGAlgebra.{u, v} R) where
  Hom A B := Hom A B
  id A := Hom.id A
  comp f g := Hom.comp g f
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- A cochain-DGA homomorphism coerces to its underlying cochain map. -/
instance instCoeCategoryHom {A B : CochainDGAlgebra.{u, v} R} :
    Coe (A ⟶ B) (A.toCochainComplex ⟶ B.toCochainComplex) where
  coe f := (f : Hom A B).toCochainMap

/-- A cochain-DGA homomorphism acts degreewise on homogeneous elements. -/
instance instCoeFunCategoryHom {A B : CochainDGAlgebra.{u, v} R} :
    CoeFun (A ⟶ B) (fun _ ↦ ∀ n : ℤ, A.X n → B.X n) where
  coe f := fun n a ↦ (f : Hom A B).map n a

/-- The raw homomorphism structure coerces to its underlying cochain map. -/
instance instCoeHom {A B : CochainDGAlgebra.{u, v} R} :
    Coe (Hom A B) (A.toCochainComplex ⟶ B.toCochainComplex) where
  coe f := f.toCochainMap

/-- The raw homomorphism structure acts degreewise on homogeneous elements. -/
instance instCoeFunHom {A : CochainDGAlgebra.{u, v} R}
    {B : CochainDGAlgebra.{u, w} R} :
    CoeFun (Hom A B) (fun _ ↦ ∀ n : ℤ, A.X n → B.X n) where
  coe f := fun n a ↦ f.map n a

/-- Coercion to a function is the degreewise action of a cochain-DGA homomorphism. -/
@[simp] theorem coe_apply {A : CochainDGAlgebra.{u, v} R}
    {B : CochainDGAlgebra.{u, w} R} (f : Hom A B) (n : ℤ) (a : A.X n) :
    f n a = f.map n a := sorry

/-- A cochain-DGA homomorphism commutes with the differential. -/
@[simp] theorem map_d_apply {A : CochainDGAlgebra.{u, v} R}
    {B : CochainDGAlgebra.{u, w} R} (f : Hom A B) (n : ℤ) (a : A.X n) :
    f (n + 1) (A.d n a) = B.d n (f n a) := sorry

/-- A cochain-DGA homomorphism preserves the unit. -/
@[simp] theorem map_one_apply {A : CochainDGAlgebra.{u, v} R}
    {B : CochainDGAlgebra.{u, w} R} (f : Hom A B) :
    f 0 A.one = B.one := sorry

/-- A cochain-DGA homomorphism preserves homogeneous multiplication. -/
@[simp] theorem map_mul_apply {A : CochainDGAlgebra.{u, v} R}
    {B : CochainDGAlgebra.{u, w} R} (f : Hom A B)
    (n m : ℤ) (a : A.X n) (b : A.X m) :
    f (n + m) (A.mul n m a b) = B.mul n m (f n a) (f m b) := sorry

/-- Cochain-DGA homomorphism composition acts degreewise by function composition. -/
@[simp] theorem comp_apply {A : CochainDGAlgebra.{u, v} R}
    {B : CochainDGAlgebra.{u, w} R} {C : CochainDGAlgebra.{u, x} R}
    (g : Hom B C) (f : Hom A B)
    (n : ℤ) (a : A.X n) :
    Hom.comp g f n a = g n (f n a) := sorry

/-- Cochain-DGA homomorphisms are determined degreewise. -/
@[ext] theorem hom_ext {A : CochainDGAlgebra.{u, v} R}
    {B : CochainDGAlgebra.{u, w} R} {f g : Hom A B}
    (h : ∀ n : ℤ, ∀ a : A.X n, f n a = g n a) : f = g := sorry

end CochainDGAlgebra
