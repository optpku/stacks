/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CotangentComplex.Transitivity
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Tensor-product cone of André-Quillen cotangent complexes

For a ring `R` and `R`-algebras `A`, `B`, this module owns the object `E` of
`D(Mod (A ⊗[R] B))` obtained as the mapping cone of the sum of the two
transitivity maps
`L_{A/R} ⊗_A (A ⊗[R] B) ⊕ L_{B/R} ⊗_B (A ⊗[R] B) ⟶ L_{A ⊗[R] B / R}`,
together with the comparison maps filling the tensor-product diagram.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open CochainComplex
open HomologicalComplex
open ComplexShape
open scoped TensorProduct

noncomputable section

universe u

namespace Algebra.CotangentComplex

/-- Underived extension of scalars of `Algebra.cotangentComplex R A` along `A → A ⊗[R] B`. -/
abbrev tensorProductExtendLeft (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    CochainComplex (ModuleCat.{u} (A ⊗[R] B)) ℤ :=
  ((ModuleCat.extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex (up ℤ)).obj
    (Algebra.cotangentComplex R A)

/-- Underived extension of scalars of `Algebra.cotangentComplex R B` along `B → A ⊗[R] B`. -/
abbrev tensorProductExtendRight (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    CochainComplex (ModuleCat.{u} (A ⊗[R] B)) ℤ :=
  ((ModuleCat.extendScalars
      ((Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom)).mapHomologicalComplex
        (up ℤ)).obj
    (Algebra.cotangentComplex R B)

/-- The relative cotangent object of the tensor product over its canonical left factor. -/
abbrev tensorProductOverA (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    DerivedCategory (ModuleCat.{u} (A ⊗[R] B)) :=
  derived A (A ⊗[R] B)

/-- The relative cotangent object of the tensor product over its canonical right factor. -/
abbrev tensorProductOverB (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    DerivedCategory (ModuleCat.{u} (A ⊗[R] B)) :=
  @derived B (A ⊗[R] B) _ _ (Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := B))

/-- The cotangent transitivity triangle through the canonical left tensor-product inclusion. -/
def tensorProductMiddleRow (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    Triangle (DerivedCategory (ModuleCat.{u} (A ⊗[R] B))) :=
  transitivityTriangle R A (A ⊗[R] B)

/-- The cotangent transitivity triangle through the canonical right tensor-product inclusion. -/
def tensorProductMiddleColumn (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    Triangle (DerivedCategory (ModuleCat.{u} (A ⊗[R] B))) :=
  (@transitivityTriangle R B (A ⊗[R] B) _ _ _ _
        (Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := B)) _
        (Algebra.TensorProduct.right_isScalarTower (R := R) (A := A) (B := B)))

/-- The cochain-level sum of the two first transitivity maps into
`Algebra.cotangentComplex R (A ⊗[R] B)`. -/
def sumMapCochain (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    (tensorProductExtendLeft R A B ⊞ tensorProductExtendRight R A B) ⟶
      Algebra.cotangentComplex R (A ⊗[R] B) :=
  biprod.desc (tensorMapCochain R A (A ⊗[R] B)) ((@tensorMapCochain R B (A ⊗[R] B) _ _ _ _
        (Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := B)) _
        (Algebra.TensorProduct.right_isScalarTower (R := R) (A := A) (B := B))))

/-- Unfolding of `sumMapCochain` as `biprod.desc` of the two `tensorMapCochain` maps. -/
theorem sumMapCochain_eq (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    sumMapCochain R A B =
      biprod.desc (tensorMapCochain R A (A ⊗[R] B)) ((@tensorMapCochain R B (A ⊗[R] B) _ _ _ _
        (Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := B)) _
        (Algebra.TensorProduct.right_isScalarTower (R := R) (A := A) (B := B)))) :=
  sorry

/-- The left inclusion into the biproduct recovers `tensorMapCochain R A (A ⊗[R] B)`. -/
theorem sumMapCochain_inl (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    biprod.inl ≫ sumMapCochain R A B = tensorMapCochain R A (A ⊗[R] B) :=
  sorry

/-- The right inclusion into the biproduct recovers `tensorMapCochain R B (A ⊗[R] B)`. -/
theorem sumMapCochain_inr (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    biprod.inr ≫ sumMapCochain R A B = (@tensorMapCochain R B (A ⊗[R] B) _ _ _ _
        (Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := B)) _
        (Algebra.TensorProduct.right_isScalarTower (R := R) (A := A) (B := B))) :=
  sorry

/-- Commutativity of the square used to induce a map of mapping cones along `biprod.inl`. -/
theorem tensorProductFromOverA_comm (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    tensorMapCochain R A (A ⊗[R] B) ≫ 𝟙 _ = biprod.inl ≫ sumMapCochain R A B :=
  sorry

/-- Commutativity of the square used to induce a map of mapping cones along `biprod.inr`. -/
theorem tensorProductFromOverB_comm (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    (@tensorMapCochain R B (A ⊗[R] B) _ _ _ _
        (Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := B)) _
        (Algebra.TensorProduct.right_isScalarTower (R := R) (A := A) (B := B))) ≫ 𝟙 _ = biprod.inr ≫ sumMapCochain R A B :=
  sorry

/-- The derived-level sum of the two first transitivity maps into
`derived R (A ⊗[R] B)`. -/
def sumMap (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    DerivedCategory.Q.obj (tensorProductExtendLeft R A B ⊞ tensorProductExtendRight R A B) ⟶
      derived R (A ⊗[R] B) :=
  DerivedCategory.Q.map (sumMapCochain R A B)

/-- Unfolding of `sumMap` as `DerivedCategory.Q.map` of `sumMapCochain`. -/
theorem sumMap_eq (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    sumMap R A B = DerivedCategory.Q.map (sumMapCochain R A B) :=
  sorry

/-- The cochain complex representing the cone of the sum of the two transitivity maps. -/
def tensorProductConeCochain (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    CochainComplex (ModuleCat.{u} (A ⊗[R] B)) ℤ :=
  mappingCone (sumMapCochain R A B)

/-- Unfolding of `tensorProductConeCochain` as a mapping cone. -/
theorem tensorProductConeCochain_eq (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    tensorProductConeCochain R A B = mappingCone (sumMapCochain R A B) :=
  sorry

/-- The object `E` of `D(Mod (A ⊗[R] B))` filling the upper-right corner of the
tensor-product diagram of cotangent complexes. -/
def tensorProductCone (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    DerivedCategory (ModuleCat.{u} (A ⊗[R] B)) :=
  DerivedCategory.Q.obj (tensorProductConeCochain R A B)

/-- Unfolding of `tensorProductCone` as `DerivedCategory.Q` of the mapping cone of
`sumMapCochain`. -/
theorem tensorProductCone_eq (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    tensorProductCone R A B = DerivedCategory.Q.obj (tensorProductConeCochain R A B) :=
  sorry

/-- The canonical map `L_{A ⊗[R] B / R} ⟶ E` induced by `mappingCone.inr`. -/
def tensorProductConeInr (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    derived R (A ⊗[R] B) ⟶ tensorProductCone R A B :=
  DerivedCategory.Q.map (mappingCone.inr (sumMapCochain R A B))

/-- Unfolding of `tensorProductConeInr` as `DerivedCategory.Q.map` of `mappingCone.inr`. -/
theorem tensorProductConeInr_eq (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    tensorProductConeInr R A B =
      DerivedCategory.Q.map (mappingCone.inr (sumMapCochain R A B)) :=
  sorry

/-- The composite from the left scalar-extended cotangent object to the right-relative object. -/
def tensorProductTopMap (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    DerivedCategory.Q.obj (tensorProductExtendLeft R A B) ⟶ tensorProductOverB R A B :=
  (tensorProductMiddleRow R A B).mor₁ ≫ (tensorProductMiddleColumn R A B).mor₂

/-- The top map factors through the two middle cotangent triangles. -/
theorem tensorProductTopMap_eq (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    tensorProductTopMap R A B =
      (tensorProductMiddleRow R A B).mor₁ ≫ (tensorProductMiddleColumn R A B).mor₂ :=
  sorry

/-- The composite from the right scalar-extended cotangent object to the left-relative object. -/
def tensorProductRightMap (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    DerivedCategory.Q.obj (tensorProductExtendRight R A B) ⟶ tensorProductOverA R A B :=
  (tensorProductMiddleColumn R A B).mor₁ ≫ (tensorProductMiddleRow R A B).mor₂

/-- The right map factors through the two middle cotangent triangles. -/
theorem tensorProductRightMap_eq (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    tensorProductRightMap R A B =
      (tensorProductMiddleColumn R A B).mor₁ ≫ (tensorProductMiddleRow R A B).mor₂ :=
  sorry

/-- The canonical localized cone comparison identifies the cone with the relative cotangent object
of the tensor product over its left factor. -/
def tensorProduct_isoOverA (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    DerivedCategory.Q.obj (mappingCone (tensorMapCochain R A (A ⊗[R] B))) ≅ tensorProductOverA R A B :=
  asIso (DerivedCategory.Q.map (fromMappingConeCochain R A (A ⊗[R] B)))

/-- The canonical localized cone comparison identifies the cone with the relative cotangent object
of the tensor product over its right factor. -/
def tensorProduct_isoOverB (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    DerivedCategory.Q.obj (mappingCone ((@tensorMapCochain R B (A ⊗[R] B) _ _ _ _
        (Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := B)) _
        (Algebra.TensorProduct.right_isScalarTower (R := R) (A := A) (B := B))))) ≅ tensorProductOverB R A B :=
  asIso (DerivedCategory.Q.map ((@fromMappingConeCochain R B (A ⊗[R] B) _ _ _ _
        (Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := B)) _
        (Algebra.TensorProduct.right_isScalarTower (R := R) (A := A) (B := B)))))

/-- The cochain-level TR3 map from the mapping cone of
`tensorMapCochain R B (A ⊗[R] B)` into the cone of `sumMapCochain`. -/
def tensorProductFromOverBCochain (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    mappingCone ((@tensorMapCochain R B (A ⊗[R] B) _ _ _ _
        (Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := B)) _
        (Algebra.TensorProduct.right_isScalarTower (R := R) (A := A) (B := B)))) ⟶ tensorProductConeCochain R A B :=
  mappingCone.map ((@tensorMapCochain R B (A ⊗[R] B) _ _ _ _
        (Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := B)) _
        (Algebra.TensorProduct.right_isScalarTower (R := R) (A := A) (B := B)))) (sumMapCochain R A B)
    biprod.inr (𝟙 _) (tensorProductFromOverB_comm R A B)

/-- The canonical map from the relative cotangent object over `B` to the sum-map cone. -/
def tensorProductFromOverB (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    tensorProductOverB R A B ⟶ tensorProductCone R A B :=
  (tensorProduct_isoOverB R A B).inv ≫
      DerivedCategory.Q.map (tensorProductFromOverBCochain R A B)

/-- The relative-to-cone map over `B` is the inverse comparison followed by the localized cone map. -/
theorem tensorProductFromOverB_eq (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    tensorProductFromOverB R A B =
      (tensorProduct_isoOverB R A B).inv ≫
      DerivedCategory.Q.map (tensorProductFromOverBCochain R A B) :=
  sorry

/-- The cochain-level TR3 map from the mapping cone of
`tensorMapCochain R A (A ⊗[R] B)` into the cone of `sumMapCochain`. -/
def tensorProductFromOverACochain (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    mappingCone (tensorMapCochain R A (A ⊗[R] B)) ⟶ tensorProductConeCochain R A B :=
  mappingCone.map (tensorMapCochain R A (A ⊗[R] B)) (sumMapCochain R A B)
    biprod.inl (𝟙 _) (tensorProductFromOverA_comm R A B)

/-- The canonical map from the relative cotangent object over `A` to the sum-map cone. -/
def tensorProductFromOverA (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    tensorProductOverA R A B ⟶ tensorProductCone R A B :=
  (tensorProduct_isoOverA R A B).inv ≫
      DerivedCategory.Q.map (tensorProductFromOverACochain R A B)

/-- The relative-to-cone map over `A` is the inverse comparison followed by the localized cone map. -/
theorem tensorProductFromOverA_eq (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    tensorProductFromOverA R A B =
      (tensorProduct_isoOverA R A B).inv ≫
      DerivedCategory.Q.map (tensorProductFromOverACochain R A B) :=
  sorry

/-- The mapping-cone triangle of `sumMapCochain` is distinguished in `D(Mod (A ⊗[R] B))`. -/
theorem tensorProductCone_triangle_distinguished (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle (sumMapCochain R A B)) ∈
      distTriang (DerivedCategory (ModuleCat.{u} (A ⊗[R] B))) :=
  sorry

/-- The middle row of the tensor-product diagram is the transitivity triangle of
`R → A → A ⊗[R] B`. -/
theorem tensorProduct_middleRow (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    tensorProductMiddleRow R A B =
      Triangle.mk (tensorMap R A (A ⊗[R] B)) (toRelativeMap R A (A ⊗[R] B))
        (connectingMap R A (A ⊗[R] B)) :=
  sorry

/-- The middle column of the tensor-product diagram is the transitivity triangle of
`R → B → A ⊗[R] B`. -/
theorem tensorProduct_middleColumn (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    tensorProductMiddleColumn R A B =
      Triangle.mk ((@tensorMap R B (A ⊗[R] B) _ _ _ _
        (Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := B)) _
        (Algebra.TensorProduct.right_isScalarTower (R := R) (A := A) (B := B)))) ((@toRelativeMap R B (A ⊗[R] B) _ _ _ _
        (Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := B)) _
        (Algebra.TensorProduct.right_isScalarTower (R := R) (A := A) (B := B))))
        ((@connectingMap R B (A ⊗[R] B) _ _ _ _
        (Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := B)) _
        (Algebra.TensorProduct.right_isScalarTower (R := R) (A := A) (B := B)))) :=
  sorry

/-- The two canonical cotangent transitivity triangles of a tensor product commute with the
sum-map cone, which completes both outer lines to distinguished triangles. -/
theorem tensorProductDiagram (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    tensorProductMiddleRow R A B ∈
      distTriang (DerivedCategory (ModuleCat.{u} (A ⊗[R] B))) ∧
    tensorProductMiddleColumn R A B ∈
      distTriang (DerivedCategory (ModuleCat.{u} (A ⊗[R] B))) ∧
    tensorProductTopMap R A B =
      (tensorProductMiddleRow R A B).mor₁ ≫ (tensorProductMiddleColumn R A B).mor₂ ∧
    tensorProductRightMap R A B =
      (tensorProductMiddleColumn R A B).mor₁ ≫ (tensorProductMiddleRow R A B).mor₂ ∧
    (tensorProductMiddleColumn R A B).mor₂ ≫ tensorProductFromOverB R A B =
      tensorProductConeInr R A B ∧
    (tensorProductMiddleRow R A B).mor₂ ≫ tensorProductFromOverA R A B =
      tensorProductConeInr R A B ∧
    ∃ (δTop : tensorProductCone R A B ⟶
        (DerivedCategory.Q.obj (tensorProductExtendLeft R A B))⟦(1 : ℤ)⟧)
      (δRight : tensorProductCone R A B ⟶
        (DerivedCategory.Q.obj (tensorProductExtendRight R A B))⟦(1 : ℤ)⟧),
      Triangle.mk (tensorProductTopMap R A B) (tensorProductFromOverB R A B) δTop ∈
        distTriang (DerivedCategory (ModuleCat.{u} (A ⊗[R] B))) ∧
      Triangle.mk (tensorProductRightMap R A B) (tensorProductFromOverA R A B) δRight ∈
        distTriang (DerivedCategory (ModuleCat.{u} (A ⊗[R] B))) :=
  sorry

end Algebra.CotangentComplex
