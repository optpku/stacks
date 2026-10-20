/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.Category
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.Commutative

/-!
# The category of strictly commutative chain DGAs

This file bundles strict graded commutativity as an object property. Morphisms are exactly the
existing chain-DGA homomorphisms, so constructions independent of divided powers can use this
category without introducing a second morphism owner.
-/

@[expose] public section

universe u v

open CategoryTheory

namespace ChainDGAlgebra

/-- A chain differential graded algebra equipped with strict graded commutativity. -/
@[stacks 09PK "infrastructure: strictly commutative chain differential graded algebras"]
structure Strict (R : Type u) [CommRing R] where
  /-- The underlying chain differential graded algebra. -/
  toChainDGAlgebra : ChainDGAlgebra.{u, v} R
  /-- The underlying chain DGA is strictly graded commutative. -/
  [isStrictlyCommutative : toChainDGAlgebra.IsStrictlyCommutative]

attribute [instance] Strict.isStrictlyCommutative

namespace Strict

variable {R : Type u} [CommRing R]

/-- Strictly commutative chain DGAs are determined by their underlying chain DGAs. -/
@[ext] theorem ext {A B : Strict.{u, v} R}
    (h : A.toChainDGAlgebra = B.toChainDGAlgebra) : A = B := sorry

/-- Strictly commutative chain DGAs form a category with the existing chain-DGA homomorphisms. -/
instance instCategory : Category (Strict.{u, v} R) where
  Hom A B := ChainDGAlgebra.Hom A.toChainDGAlgebra B.toChainDGAlgebra
  id A := ChainDGAlgebra.Hom.id A.toChainDGAlgebra
  comp f g := ChainDGAlgebra.Hom.comp g f
  id_comp := ChainDGAlgebra.Hom.id_comp
  comp_id := ChainDGAlgebra.Hom.comp_id
  assoc := ChainDGAlgebra.Hom.comp_assoc

/-- A morphism of strictly commutative chain DGAs acts degreewise on homogeneous elements. -/
instance instCoeFun {A B : Strict.{u, v} R} :
    CoeFun (A ⟶ B) (fun _ ↦ ∀ n : ℤ,
      A.toChainDGAlgebra.X n → B.toChainDGAlgebra.X n) where
  coe f := fun n x ↦
    (f : ChainDGAlgebra.Hom A.toChainDGAlgebra B.toChainDGAlgebra).toChainMap.f n x

/-- Degreewise evaluation of a strict morphism is evaluation of its underlying chain map. -/
@[simp] theorem coe_apply {A B : Strict.{u, v} R} (f : A ⟶ B) (n : ℤ)
    (x : A.toChainDGAlgebra.X n) :
    f n x =
      (f : ChainDGAlgebra.Hom A.toChainDGAlgebra B.toChainDGAlgebra).toChainMap.f n x := sorry

/-- The identity map is preserved by forgetting strict commutativity. -/
theorem forgetMap_id (A : Strict.{u, v} R) :
    (ChainDGAlgebra.Hom.id A.toChainDGAlgebra :
      A.toChainDGAlgebra ⟶ A.toChainDGAlgebra) =
        𝟙 A.toChainDGAlgebra := sorry

/-- Composition is preserved by forgetting strict commutativity. -/
theorem forgetMap_comp {A B C : Strict.{u, v} R} (f : A ⟶ B) (g : B ⟶ C) :
    (ChainDGAlgebra.Hom.comp g f : A.toChainDGAlgebra ⟶ C.toChainDGAlgebra) =
      (f : A.toChainDGAlgebra ⟶ B.toChainDGAlgebra) ≫
        (g : B.toChainDGAlgebra ⟶ C.toChainDGAlgebra) := sorry

/-- Forget strict graded commutativity while retaining the underlying chain DGA and its map. -/
def forget (R : Type u) [CommRing R] :
    Strict.{u, v} R ⥤ ChainDGAlgebra.{u, v} R where
  obj A := A.toChainDGAlgebra
  map f := f
  map_id A := forgetMap_id A
  map_comp f g := forgetMap_comp f g

/-- Forgetting a strict object returns its underlying chain DGA. -/
@[simp] theorem forget_obj (A : Strict.{u, v} R) :
    (forget R).obj A = A.toChainDGAlgebra := sorry

/-- Forgetting a morphism retains the same chain-DGA homomorphism. -/
@[simp] theorem forget_map {A B : Strict.{u, v} R} (f : A ⟶ B) :
    (forget R).map f = f := sorry

end Strict

end ChainDGAlgebra

#synth Category (ChainDGAlgebra.Strict ℤ)
