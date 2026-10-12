/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.«92_7_0_1_Triangle»
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
    [Algebra R A] [Algebra R B] [Algebra A (A ⊗[R] B)] :
    CochainComplex (ModuleCat.{u} (A ⊗[R] B)) ℤ :=
  ((ModuleCat.extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex (up ℤ)).obj
    (Algebra.cotangentComplex R A)

/-- Underived extension of scalars of `Algebra.cotangentComplex R B` along `B → A ⊗[R] B`. -/
abbrev tensorProductExtendRight (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra B (A ⊗[R] B)] :
    CochainComplex (ModuleCat.{u} (A ⊗[R] B)) ℤ :=
  ((ModuleCat.extendScalars (algebraMap B (A ⊗[R] B))).mapHomologicalComplex (up ℤ)).obj
    (Algebra.cotangentComplex R B)

/-- The cochain-level sum of the two first transitivity maps into
`Algebra.cotangentComplex R (A ⊗[R] B)`. -/
def sumMapCochain (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra B (A ⊗[R] B)]
    [IsScalarTower R A (A ⊗[R] B)] [IsScalarTower R B (A ⊗[R] B)] :
    (tensorProductExtendLeft R A B ⊞ tensorProductExtendRight R A B) ⟶
      Algebra.cotangentComplex R (A ⊗[R] B) :=
  biprod.desc (tensorMapCochain R A (A ⊗[R] B)) (tensorMapCochain R B (A ⊗[R] B))

/-- Unfolding of `sumMapCochain` as `biprod.desc` of the two `tensorMapCochain` maps. -/
theorem sumMapCochain_eq (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra B (A ⊗[R] B)]
    [IsScalarTower R A (A ⊗[R] B)] [IsScalarTower R B (A ⊗[R] B)] :
    sumMapCochain R A B =
      biprod.desc (tensorMapCochain R A (A ⊗[R] B)) (tensorMapCochain R B (A ⊗[R] B)) :=
  sorry

/-- The left inclusion into the biproduct recovers `tensorMapCochain R A (A ⊗[R] B)`. -/
theorem sumMapCochain_inl (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra B (A ⊗[R] B)]
    [IsScalarTower R A (A ⊗[R] B)] [IsScalarTower R B (A ⊗[R] B)] :
    biprod.inl ≫ sumMapCochain R A B = tensorMapCochain R A (A ⊗[R] B) :=
  sorry

/-- The right inclusion into the biproduct recovers `tensorMapCochain R B (A ⊗[R] B)`. -/
theorem sumMapCochain_inr (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra B (A ⊗[R] B)]
    [IsScalarTower R A (A ⊗[R] B)] [IsScalarTower R B (A ⊗[R] B)] :
    biprod.inr ≫ sumMapCochain R A B = tensorMapCochain R B (A ⊗[R] B) :=
  sorry

/-- Commutativity of the square used to induce a map of mapping cones along `biprod.inl`. -/
theorem tensorProductFromOverA_comm (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra B (A ⊗[R] B)]
    [IsScalarTower R A (A ⊗[R] B)] [IsScalarTower R B (A ⊗[R] B)] :
    tensorMapCochain R A (A ⊗[R] B) ≫ 𝟙 _ = biprod.inl ≫ sumMapCochain R A B :=
  sorry

/-- Commutativity of the square used to induce a map of mapping cones along `biprod.inr`. -/
theorem tensorProductFromOverB_comm (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra B (A ⊗[R] B)]
    [IsScalarTower R A (A ⊗[R] B)] [IsScalarTower R B (A ⊗[R] B)] :
    tensorMapCochain R B (A ⊗[R] B) ≫ 𝟙 _ = biprod.inr ≫ sumMapCochain R A B :=
  sorry

/-- The derived-level sum of the two first transitivity maps into
`derived R (A ⊗[R] B)`. -/
def sumMap (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra B (A ⊗[R] B)]
    [IsScalarTower R A (A ⊗[R] B)] [IsScalarTower R B (A ⊗[R] B)] :
    DerivedCategory.Q.obj (tensorProductExtendLeft R A B ⊞ tensorProductExtendRight R A B) ⟶
      derived R (A ⊗[R] B) :=
  DerivedCategory.Q.map (sumMapCochain R A B)

/-- Unfolding of `sumMap` as `DerivedCategory.Q.map` of `sumMapCochain`. -/
theorem sumMap_eq (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra B (A ⊗[R] B)]
    [IsScalarTower R A (A ⊗[R] B)] [IsScalarTower R B (A ⊗[R] B)] :
    sumMap R A B = DerivedCategory.Q.map (sumMapCochain R A B) :=
  sorry

/-- The cochain complex representing the cone of the sum of the two transitivity maps. -/
def tensorProductConeCochain (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra B (A ⊗[R] B)]
    [IsScalarTower R A (A ⊗[R] B)] [IsScalarTower R B (A ⊗[R] B)] :
    CochainComplex (ModuleCat.{u} (A ⊗[R] B)) ℤ :=
  mappingCone (sumMapCochain R A B)

/-- Unfolding of `tensorProductConeCochain` as a mapping cone. -/
theorem tensorProductConeCochain_eq (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra B (A ⊗[R] B)]
    [IsScalarTower R A (A ⊗[R] B)] [IsScalarTower R B (A ⊗[R] B)] :
    tensorProductConeCochain R A B = mappingCone (sumMapCochain R A B) :=
  sorry

/-- The object `E` of `D(Mod (A ⊗[R] B))` filling the upper-right corner of the
tensor-product diagram of cotangent complexes. -/
def tensorProductCone (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra B (A ⊗[R] B)]
    [IsScalarTower R A (A ⊗[R] B)] [IsScalarTower R B (A ⊗[R] B)] :
    DerivedCategory (ModuleCat.{u} (A ⊗[R] B)) :=
  DerivedCategory.Q.obj (tensorProductConeCochain R A B)

/-- Unfolding of `tensorProductCone` as `DerivedCategory.Q` of the mapping cone of
`sumMapCochain`. -/
theorem tensorProductCone_eq (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra B (A ⊗[R] B)]
    [IsScalarTower R A (A ⊗[R] B)] [IsScalarTower R B (A ⊗[R] B)] :
    tensorProductCone R A B = DerivedCategory.Q.obj (tensorProductConeCochain R A B) :=
  sorry

/-- The canonical map `L_{A ⊗[R] B / R} ⟶ E` induced by `mappingCone.inr`. -/
def tensorProductConeInr (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra B (A ⊗[R] B)]
    [IsScalarTower R A (A ⊗[R] B)] [IsScalarTower R B (A ⊗[R] B)] :
    derived R (A ⊗[R] B) ⟶ tensorProductCone R A B :=
  DerivedCategory.Q.map (mappingCone.inr (sumMapCochain R A B))

/-- Unfolding of `tensorProductConeInr` as `DerivedCategory.Q.map` of `mappingCone.inr`. -/
theorem tensorProductConeInr_eq (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra B (A ⊗[R] B)]
    [IsScalarTower R A (A ⊗[R] B)] [IsScalarTower R B (A ⊗[R] B)] :
    tensorProductConeInr R A B =
      DerivedCategory.Q.map (mappingCone.inr (sumMapCochain R A B)) :=
  sorry

/-- The first arrow of the top row,
`L_{A/R} ⊗^L_A (A ⊗[R] B) ⟶ L_{A ⊗[R] B / B}`. -/
def tensorProductTopMap (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra B (A ⊗[R] B)]
    [IsScalarTower R A (A ⊗[R] B)] [IsScalarTower R B (A ⊗[R] B)] :
    tensor R A (A ⊗[R] B) ⟶ derived B (A ⊗[R] B) :=
  tensorMap R A (A ⊗[R] B) ≫ toRelativeMap R B (A ⊗[R] B)

/-- Unfolding of `tensorProductTopMap` as the composite through `derived R (A ⊗[R] B)`. -/
theorem tensorProductTopMap_eq (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra B (A ⊗[R] B)]
    [IsScalarTower R A (A ⊗[R] B)] [IsScalarTower R B (A ⊗[R] B)] :
    tensorProductTopMap R A B =
      tensorMap R A (A ⊗[R] B) ≫ toRelativeMap R B (A ⊗[R] B) :=
  sorry

/-- The first arrow of the right column,
`L_{B/R} ⊗^L_B (A ⊗[R] B) ⟶ L_{A ⊗[R] B / A}`. -/
def tensorProductRightMap (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra B (A ⊗[R] B)]
    [IsScalarTower R A (A ⊗[R] B)] [IsScalarTower R B (A ⊗[R] B)] :
    tensor R B (A ⊗[R] B) ⟶ derived A (A ⊗[R] B) :=
  tensorMap R B (A ⊗[R] B) ≫ toRelativeMap R A (A ⊗[R] B)

/-- Unfolding of `tensorProductRightMap` as the composite through `derived R (A ⊗[R] B)`. -/
theorem tensorProductRightMap_eq (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra B (A ⊗[R] B)]
    [IsScalarTower R A (A ⊗[R] B)] [IsScalarTower R B (A ⊗[R] B)] :
    tensorProductRightMap R A B =
      tensorMap R B (A ⊗[R] B) ≫ toRelativeMap R A (A ⊗[R] B) :=
  sorry

/-- The cochain-level TR3 map from the mapping cone of
`tensorMapCochain R B (A ⊗[R] B)` into the cone of `sumMapCochain`. -/
def tensorProductFromOverBCochain (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra B (A ⊗[R] B)]
    [IsScalarTower R A (A ⊗[R] B)] [IsScalarTower R B (A ⊗[R] B)] :
    mappingCone (tensorMapCochain R B (A ⊗[R] B)) ⟶ tensorProductConeCochain R A B :=
  mappingCone.map (tensorMapCochain R B (A ⊗[R] B)) (sumMapCochain R A B)
    biprod.inr (𝟙 _) (tensorProductFromOverB_comm R A B)

/-- The derived-level TR3 map from the mapping-cone model of `L_{A ⊗[R] B / B}` into `E`. -/
def tensorProductFromOverB (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra B (A ⊗[R] B)]
    [IsScalarTower R A (A ⊗[R] B)] [IsScalarTower R B (A ⊗[R] B)] :
    DerivedCategory.Q.obj (mappingCone (tensorMapCochain R B (A ⊗[R] B))) ⟶
      tensorProductCone R A B :=
  DerivedCategory.Q.map (tensorProductFromOverBCochain R A B)

/-- Unfolding of `tensorProductFromOverB` as `DerivedCategory.Q.map` of the cochain TR3 map. -/
theorem tensorProductFromOverB_eq (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra B (A ⊗[R] B)]
    [IsScalarTower R A (A ⊗[R] B)] [IsScalarTower R B (A ⊗[R] B)] :
    tensorProductFromOverB R A B =
      DerivedCategory.Q.map (tensorProductFromOverBCochain R A B) :=
  sorry

/-- The cochain-level TR3 map from the mapping cone of
`tensorMapCochain R A (A ⊗[R] B)` into the cone of `sumMapCochain`. -/
def tensorProductFromOverACochain (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra B (A ⊗[R] B)]
    [IsScalarTower R A (A ⊗[R] B)] [IsScalarTower R B (A ⊗[R] B)] :
    mappingCone (tensorMapCochain R A (A ⊗[R] B)) ⟶ tensorProductConeCochain R A B :=
  mappingCone.map (tensorMapCochain R A (A ⊗[R] B)) (sumMapCochain R A B)
    biprod.inl (𝟙 _) (tensorProductFromOverA_comm R A B)

/-- The derived-level TR3 map from the mapping-cone model of `L_{A ⊗[R] B / A}` into `E`. -/
def tensorProductFromOverA (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra B (A ⊗[R] B)]
    [IsScalarTower R A (A ⊗[R] B)] [IsScalarTower R B (A ⊗[R] B)] :
    DerivedCategory.Q.obj (mappingCone (tensorMapCochain R A (A ⊗[R] B))) ⟶
      tensorProductCone R A B :=
  DerivedCategory.Q.map (tensorProductFromOverACochain R A B)

/-- Unfolding of `tensorProductFromOverA` as `DerivedCategory.Q.map` of the cochain TR3 map. -/
theorem tensorProductFromOverA_eq (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra B (A ⊗[R] B)]
    [IsScalarTower R A (A ⊗[R] B)] [IsScalarTower R B (A ⊗[R] B)] :
    tensorProductFromOverA R A B =
      DerivedCategory.Q.map (tensorProductFromOverACochain R A B) :=
  sorry

/-- The mapping-cone triangle of `sumMapCochain` is distinguished in `D(Mod (A ⊗[R] B))`. -/
theorem tensorProductCone_triangle_distinguished (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra B (A ⊗[R] B)]
    [IsScalarTower R A (A ⊗[R] B)] [IsScalarTower R B (A ⊗[R] B)] :
    DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle (sumMapCochain R A B)) ∈
      distTriang (DerivedCategory (ModuleCat.{u} (A ⊗[R] B))) :=
  sorry

/-- The middle row of the tensor-product diagram is the transitivity triangle of
`R → A → A ⊗[R] B`. -/
theorem tensorProduct_middleRow (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra B (A ⊗[R] B)]
    [IsScalarTower R A (A ⊗[R] B)] [IsScalarTower R B (A ⊗[R] B)] :
    transitivityTriangle R A (A ⊗[R] B) =
      Triangle.mk (tensorMap R A (A ⊗[R] B)) (toRelativeMap R A (A ⊗[R] B))
        (connectingMap R A (A ⊗[R] B)) :=
  sorry

/-- The middle column of the tensor-product diagram is the transitivity triangle of
`R → B → A ⊗[R] B`. -/
theorem tensorProduct_middleColumn (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra B (A ⊗[R] B)]
    [IsScalarTower R A (A ⊗[R] B)] [IsScalarTower R B (A ⊗[R] B)] :
    transitivityTriangle R B (A ⊗[R] B) =
      Triangle.mk (tensorMap R B (A ⊗[R] B)) (toRelativeMap R B (A ⊗[R] B))
        (connectingMap R B (A ⊗[R] B)) :=
  sorry

/-- The mapping cone of `tensorMapCochain R B (A ⊗[R] B)` models `L_{A ⊗[R] B / B}`
up to isomorphism in `D(Mod (A ⊗[R] B))`. -/
theorem tensorProduct_isoOverB (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra B (A ⊗[R] B)]
    [IsScalarTower R A (A ⊗[R] B)] [IsScalarTower R B (A ⊗[R] B)] :
    Nonempty
      (DerivedCategory.Q.obj (mappingCone (tensorMapCochain R B (A ⊗[R] B))) ≅
        derived B (A ⊗[R] B)) :=
  sorry

/-- The mapping cone of `tensorMapCochain R A (A ⊗[R] B)` models `L_{A ⊗[R] B / A}`
up to isomorphism in `D(Mod (A ⊗[R] B))`. -/
theorem tensorProduct_isoOverA (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra B (A ⊗[R] B)]
    [IsScalarTower R A (A ⊗[R] B)] [IsScalarTower R B (A ⊗[R] B)] :
    Nonempty
      (DerivedCategory.Q.obj (mappingCone (tensorMapCochain R A (A ⊗[R] B))) ≅
        derived A (A ⊗[R] B)) :=
  sorry

end Algebra.CotangentComplex
