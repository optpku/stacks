/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Single
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Restrict
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import ReasLib.Algebra.Homology.Embedding.Functor
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import ReasLib.CategoryTheory.Shift.ShiftedHom.Adjunction
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.BaseChange
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.BaseChange.Derived
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction.Single
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.ExtendScalars
public import ReasLib.RingTheory.RingHom.SquareZero.Fiber

universe u

@[expose] public section

noncomputable section

namespace RingHom.SquareZeroExtension

open CategoryTheory DerivedCategory HomologicalComplex ComplexShape
open CategoryTheory.Pretriangulated
open Algebra Algebra.Generators Algebra.Extension
open Algebra.Extension.NaiveCotangent
open Algebra.NaiveCotangent.DerivedBaseChange
open RingHom.SquareZeroExtension
open scoped DerivedExt NaiveCotangent DerivedTensorWithAlgebra

variable {A' A : Type u} [CommRing A'] [CommRing A]
variable (π : A' →+* A) [π.IsSquareZeroExtension]
variable (B : Type u) [CommRing B] [Algebra A B]
variable {N : Type u} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]

/-- The underived base change `NL{A⁄A'} ⊗[A] B`, as an object of `D(ModuleCat B)`. -/
def underivedTensorObject :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    DerivedCategory (ModuleCat B) :=
  -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
  letI := algebraOfSquareZero π
  Q.obj ((NaiveCotangent.BaseChange.tensorModel
      (Generators.self A' A).toExtension).extend embeddingDownNat)

/-- `underivedTensorObject` is the derived image of the extended tensor model of `NL{A⁄A'}`. -/
theorem underivedTensorObject_eq :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    underivedTensorObject π B =
      Q.obj ((NaiveCotangent.BaseChange.tensorModel
          (Generators.self A' A).toExtension).extend embeddingDownNat) := sorry

/-- The additive derived Ext¹ identification from restriction of scalars to derived extension
of scalars for the naive cotangent object. -/
def extOne_adjunction (π : A' →+* A) [π.IsSquareZeroExtension]
    (B : Type u) [CommRing B] [Algebra A B]
    {N : Type u} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N] :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    Ext⁽(1 : ℤ)⁾(Algebra.naiveCotangentObject A' A,
        (ModuleCat.derivedRestrictionOfScalars (algebraMap A B)).obj
          ((singleFunctor (ModuleCat B) (0 : ℤ)).obj (ModuleCat.of B N))) ≃+
      Ext⁽(1 : ℤ)⁾(Algebra.naiveCotangentObject A' A ⊗[A]^L[B],
        (singleFunctor (ModuleCat B) (0 : ℤ)).obj (ModuleCat.of B N)) :=
  -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
  letI := algebraOfSquareZero π
  ((ModuleCat.derivedExtensionRestrictionAdjunction (algebraMap A B)).shiftedHomLinearEquiv
    (R := ℤ) (Algebra.naiveCotangentObject A' A)
    ((singleFunctor (ModuleCat B) (0 : ℤ)).obj (ModuleCat.of B N))
    (1 : ℤ)).toAddEquiv

/-- The derived-to-underived comparison of `NL{A⁄A'}` along `A → B`. -/
def underivedComparison :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    Algebra.naiveCotangentObject A' A ⊗[A]^L[B] ⟶ underivedTensorObject π B :=
  -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
  letI := algebraOfSquareZero π
  -- Local instance justification (noncanonical choice): Algebra A' B is determined by the composite of π with algebraMap A B.
  letI := algebraCompOfSquareZero π B
  -- Local instance justification (defeq pin): the tower A' → A → B is the composite of the algebra maps of π.
  letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
  selfComparison ≫
    Q.map
      ((ComplexShape.Embedding.mapAppIso embeddingDownNat
          (ModuleCat.extendScalars (algebraMap A B))
          (Algebra.naiveCotangent A' A)).hom ≫
        extendMap
          (NaiveCotangent.BaseChange.scalarExtensionIsoTensorModel
            (Generators.self A' A).toExtension).hom
          embeddingDownNat)

/-- `underivedComparison` is `selfComparison` followed by the scalar-extension/tensor-model iso. -/
theorem underivedComparison_eq :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    -- Local instance justification (noncanonical choice): Algebra A' B is determined by the composite of π with algebraMap A B.
    letI := algebraCompOfSquareZero π B
    -- Local instance justification (defeq pin): the tower A' → A → B is the composite of the algebra maps of π.
    letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
    underivedComparison π B =
      selfComparison ≫
        Q.map
          ((ComplexShape.Embedding.mapAppIso embeddingDownNat
              (ModuleCat.extendScalars (algebraMap A B))
              (Algebra.naiveCotangent A' A)).hom ≫
            extendMap
              (NaiveCotangent.BaseChange.scalarExtensionIsoTensorModel
                (Generators.self A' A).toExtension).hom
              embeddingDownNat) := sorry

/-- Precomposition with `underivedComparison` on Ext¹ with coefficients `N`. -/
def extOne_underived_precomp :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    Ext⁽(1 : ℤ)⁾(underivedTensorObject π B,
        (singleFunctor (ModuleCat B) (0 : ℤ)).obj (ModuleCat.of B N)) →
      Ext⁽(1 : ℤ)⁾(Algebra.naiveCotangentObject A' A ⊗[A]^L[B],
        (singleFunctor (ModuleCat B) (0 : ℤ)).obj (ModuleCat.of B N)) :=
  fun ξ ↦
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    underivedComparison π B ≫ ξ

/-- Precomposition with the derived-to-underived comparison identifies Ext¹ of the
underived tensor object with Ext¹ of the derived base change. -/
theorem extOne_underived :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    Function.Bijective
      (extOne_underived_precomp π B :
        Ext⁽(1 : ℤ)⁾(underivedTensorObject π B,
            (singleFunctor (ModuleCat B) (0 : ℤ)).obj (ModuleCat.of B N)) →
          Ext⁽(1 : ℤ)⁾(Algebra.naiveCotangentObject A' A ⊗[A]^L[B],
            (singleFunctor (ModuleCat B) (0 : ℤ)).obj (ModuleCat.of B N))) := sorry

/-- The canonical map of complexes from the tensor model to the base-changed naive cotangent complex.
`NL{A⁄A'} ⊗[A] B ⟶ NL{B⁄A'}` induced by the self-presentations. -/
def baseChangeMap :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    -- Local instance justification (noncanonical choice): Algebra A' B is determined by the composite of π with algebraMap A B.
    letI := algebraCompOfSquareZero π B
    -- Local instance justification (defeq pin): the tower A' → A → B is the composite of the algebra maps of π.
    letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
    NaiveCotangent.BaseChange.tensorModel (Generators.self A' A).toExtension ⟶
      Algebra.naiveCotangent A' B :=
  -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
  letI := algebraOfSquareZero π
  -- Local instance justification (noncanonical choice): Algebra A' B is determined by the composite of π with algebraMap A B.
  letI := algebraCompOfSquareZero π B
  -- Local instance justification (defeq pin): the tower A' → A → B is the composite of the algebra maps of π.
  letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
  (NaiveCotangent.BaseChange.scalarExtensionIsoTensorModel
      (Generators.self A' A).toExtension).inv ≫
    NaiveCotangent.ExtendScalars.map
      (Generators.defaultHom (Generators.self A' A) (Generators.self A' B)).toExtensionHom

/-- `baseChangeMap` is the tensor-model inverse followed by `ExtendScalars.map` of the
default self-presentation hom. -/
theorem baseChangeMap_eq :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    -- Local instance justification (noncanonical choice): Algebra A' B is determined by the composite of π with algebraMap A B.
    letI := algebraCompOfSquareZero π B
    -- Local instance justification (defeq pin): the tower A' → A → B is the composite of the algebra maps of π.
    letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
    baseChangeMap π B =
      (NaiveCotangent.BaseChange.scalarExtensionIsoTensorModel
          (Generators.self A' A).toExtension).inv ≫
        NaiveCotangent.ExtendScalars.map
          (Generators.defaultHom (Generators.self A' A)
            (Generators.self A' B)).toExtensionHom := sorry

/-- The canonical change-of-base-ring map `NL{B⁄A'} ⟶ NL{B⁄A}` induced by the
self-presentations. -/
def sourceChangeMap :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    -- Local instance justification (noncanonical choice): Algebra A' B is determined by the composite of π with algebraMap A B.
    letI := algebraCompOfSquareZero π B
    -- Local instance justification (defeq pin): the tower A' → A → B is the composite of the algebra maps of π.
    letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
    Algebra.naiveCotangent A' B ⟶ Algebra.naiveCotangent A B :=
  -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
  letI := algebraOfSquareZero π
  -- Local instance justification (noncanonical choice): Algebra A' B is determined by the composite of π with algebraMap A B.
  letI := algebraCompOfSquareZero π B
  -- Local instance justification (defeq pin): the tower A' → A → B is the composite of the algebra maps of π.
  letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
  NaiveCotangent.chainMap
    (Generators.defaultHom (Generators.self A' B) (Generators.self A B)).toExtensionHom

/-- `sourceChangeMap` is `chainMap` of the default hom from the self-presentation of B
over A' to that of B over A. -/
theorem sourceChangeMap_eq :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    -- Local instance justification (noncanonical choice): Algebra A' B is determined by the composite of π with algebraMap A B.
    letI := algebraCompOfSquareZero π B
    -- Local instance justification (defeq pin): the tower A' → A → B is the composite of the algebra maps of π.
    letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
    sourceChangeMap π B =
      NaiveCotangent.chainMap
        (Generators.defaultHom (Generators.self A' B)
          (Generators.self A B)).toExtensionHom := sorry

/-- The derived image of `baseChangeMap`. -/
def baseChangeMapDerived :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    -- Local instance justification (noncanonical choice): Algebra A' B is determined by the composite of π with algebraMap A B.
    letI := algebraCompOfSquareZero π B
    -- Local instance justification (defeq pin): the tower A' → A → B is the composite of the algebra maps of π.
    letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
    underivedTensorObject π B ⟶ Algebra.naiveCotangentObject A' B :=
  -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
  letI := algebraOfSquareZero π
  -- Local instance justification (noncanonical choice): Algebra A' B is determined by the composite of π with algebraMap A B.
  letI := algebraCompOfSquareZero π B
  -- Local instance justification (defeq pin): the tower A' → A → B is the composite of the algebra maps of π.
  letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
  Q.map (extendMap (baseChangeMap π B) embeddingDownNat)

/-- `baseChangeMapDerived` is `Q.map` of the extended chain map `baseChangeMap`. -/
theorem baseChangeMapDerived_eq :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    -- Local instance justification (noncanonical choice): Algebra A' B is determined by the composite of π with algebraMap A B.
    letI := algebraCompOfSquareZero π B
    -- Local instance justification (defeq pin): the tower A' → A → B is the composite of the algebra maps of π.
    letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
    baseChangeMapDerived π B =
      Q.map (extendMap (baseChangeMap π B) embeddingDownNat) := sorry

/-- The derived image of `sourceChangeMap`. -/
def sourceChangeMapDerived :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    -- Local instance justification (noncanonical choice): Algebra A' B is determined by the composite of π with algebraMap A B.
    letI := algebraCompOfSquareZero π B
    -- Local instance justification (defeq pin): the tower A' → A → B is the composite of the algebra maps of π.
    letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
    Algebra.naiveCotangentObject A' B ⟶ Algebra.naiveCotangentObject A B :=
  -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
  letI := algebraOfSquareZero π
  -- Local instance justification (noncanonical choice): Algebra A' B is determined by the composite of π with algebraMap A B.
  letI := algebraCompOfSquareZero π B
  -- Local instance justification (defeq pin): the tower A' → A → B is the composite of the algebra maps of π.
  letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
  Q.map (extendMap (sourceChangeMap π B) embeddingDownNat)

/-- `sourceChangeMapDerived` is `Q.map` of the extended chain map `sourceChangeMap`. -/
theorem sourceChangeMapDerived_eq :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    -- Local instance justification (noncanonical choice): Algebra A' B is determined by the composite of π with algebraMap A B.
    letI := algebraCompOfSquareZero π B
    -- Local instance justification (defeq pin): the tower A' → A → B is the composite of the algebra maps of π.
    letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
    sourceChangeMapDerived π B =
      Q.map (extendMap (sourceChangeMap π B) embeddingDownNat) := sorry

/-- The connecting Ext² class of a class in Ext¹ of the underived tensor, given an
explicit connecting morphism `γ : NL{B⁄A} ⟶ (NL{A⁄A'} ⊗[A] B)⟦1⟧`. -/
def connectingExtTwo
    (γ :
      -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
      letI := algebraOfSquareZero π
      Algebra.naiveCotangentObject A B ⟶ (underivedTensorObject π B)⟦(1 : ℤ)⟧)
    (ξ :
      -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
      letI := algebraOfSquareZero π
      Ext⁽(1 : ℤ)⁾(underivedTensorObject π B,
        (singleFunctor (ModuleCat B) (0 : ℤ)).obj (ModuleCat.of B N))) :
    Ext⁽(2 : ℤ)⁾(Algebra.naiveCotangentObject A B,
      (singleFunctor (ModuleCat B) (0 : ℤ)).obj (ModuleCat.of B N)) :=
  ShiftedHom.comp γ ξ rfl

/-- `connectingExtTwo` is `ShiftedHom.comp` of `γ` with the Ext¹ class. -/
theorem connectingExtTwo_spec
    (γ :
      -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
      letI := algebraOfSquareZero π
      Algebra.naiveCotangentObject A B ⟶ (underivedTensorObject π B)⟦(1 : ℤ)⟧)
    (ξ :
      -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
      letI := algebraOfSquareZero π
      Ext⁽(1 : ℤ)⁾(underivedTensorObject π B,
        (singleFunctor (ModuleCat B) (0 : ℤ)).obj (ModuleCat.of B N))) :
    connectingExtTwo π B γ ξ = ShiftedHom.comp γ ξ rfl := sorry

/-- The degree-one component of a Hom representative of Ext¹_A(NL{A⁄A'}, N). -/
def extOne_cotangentHom_one
    (f :
      -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
      letI := algebraOfSquareZero π
      (Generators.self A' A).toExtension.Cotangent →ₗ[A] N) :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    (Algebra.naiveCotangent A' A).X 1 ⟶ ModuleCat.of A N :=
  -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
  letI := algebraOfSquareZero π
  let P := (Generators.self A' A).toExtension
  (componentOneIso P).hom ≫
    ModuleCat.ofHom
      (f ∘ₗ (liftEquiv P).toLinearMap)

/-- `extOne_cotangentHom_one` is the component-one iso followed by the lifted conormal map. -/
theorem extOne_cotangentHom_one_eq
    (f :
      -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
      letI := algebraOfSquareZero π
      (Generators.self A' A).toExtension.Cotangent →ₗ[A] N) :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    extOne_cotangentHom_one π f =
      (componentOneIso
          (Generators.self A' A).toExtension).hom ≫
        ModuleCat.ofHom
          (f ∘ₗ (liftEquiv
              (Generators.self A' A).toExtension).toLinearMap) := rfl

/-- Differentials into degree one vanish after `extOne_cotangentHom_one`. -/
theorem extOne_cotangentHom_d_comp
    (f :
      -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
      letI := algebraOfSquareZero π
      (Generators.self A' A).toExtension.Cotangent →ₗ[A] N)
    (i : ℕ) (hi : (ComplexShape.down ℕ).Rel i 1) :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    (Algebra.naiveCotangent A' A).d i 1 ≫ extOne_cotangentHom_one π f = 0 := sorry

/-- The chain map `NL{A⁄A'} ⟶ N[1]` attached to a Hom representative of
Ext¹_A(NL{A⁄A'}, N). -/
def extOne_cotangentHom
    (f :
      -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
      letI := algebraOfSquareZero π
      (Generators.self A' A).toExtension.Cotangent →ₗ[A] N) :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    Algebra.naiveCotangent A' A ⟶
      (HomologicalComplex.single (ModuleCat A) (ComplexShape.down ℕ) 1).obj
        (ModuleCat.of A N) :=
  -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
  letI := algebraOfSquareZero π
  HomologicalComplex.mkHomToSingle (extOne_cotangentHom_one π f)
    (extOne_cotangentHom_d_comp π f)

/-- `extOne_cotangentHom` is `mkHomToSingle` of the degree-one Hom representative. -/
theorem extOne_cotangentHom_eq
    (f :
      -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
      letI := algebraOfSquareZero π
      (Generators.self A' A).toExtension.Cotangent →ₗ[A] N) :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    extOne_cotangentHom π f =
      HomologicalComplex.mkHomToSingle (extOne_cotangentHom_one π f)
        (extOne_cotangentHom_d_comp π f) := rfl

/-- The derived Ext¹ class of a Hom representative of Ext¹_A(NL{A⁄A'}, N), aligned
with restriction of scalars of `N[0]` along `A → B`. -/
def toDerived
    (f :
      -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
      letI := algebraOfSquareZero π
      (Generators.self A' A).toExtension.Cotangent →ₗ[A] N) :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    Ext⁽(1 : ℤ)⁾(Algebra.naiveCotangentObject A' A,
      (ModuleCat.derivedRestrictionOfScalars (algebraMap A B)).obj
        ((singleFunctor (ModuleCat B) (0 : ℤ)).obj (ModuleCat.of B N))) :=
  -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
  letI := algebraOfSquareZero π
  Q.map (extendMap (extOne_cotangentHom π f) embeddingDownNat) ≫
    Q.map
      (extendSingleIso embeddingDownNat (ModuleCat.of A N) 1 (-1 : ℤ) rfl).hom ≫
    ((DerivedCategory.singleFunctors (ModuleCat A)).shiftIso (1 : ℤ) (-1) 0
        (add_neg_cancel (1 : ℤ))).inv.app (ModuleCat.of A N) ≫
      (((singleFunctor (ModuleCat A) (0 : ℤ)).map
          (ModuleCat.RestrictScalars.identityIso (R := A) (S := B) N).inv)⟦(1 : ℤ)⟧') ≫
        ((ModuleCat.DerivedRestriction.singleIso (algebraMap A B) (0 : ℤ)
            (ModuleCat.of B N)).inv⟦(1 : ℤ)⟧')

/-- `toDerived` is the derived image of `extOne_cotangentHom`, transported to the
restriction of `N[0]`. -/
theorem toDerived_eq
    (f :
      -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
      letI := algebraOfSquareZero π
      (Generators.self A' A).toExtension.Cotangent →ₗ[A] N) :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    toDerived π B f =
      Q.map (extendMap (extOne_cotangentHom π f) embeddingDownNat) ≫
        Q.map
          (extendSingleIso embeddingDownNat (ModuleCat.of A N) 1 (-1 : ℤ) rfl).hom ≫
        ((DerivedCategory.singleFunctors (ModuleCat A)).shiftIso (1 : ℤ) (-1) 0
            (add_neg_cancel (1 : ℤ))).inv.app (ModuleCat.of A N) ≫
          (((singleFunctor (ModuleCat A) (0 : ℤ)).map
              (ModuleCat.RestrictScalars.identityIso (R := A) (S := B) N).inv)⟦(1 : ℤ)⟧') ≫
            ((ModuleCat.DerivedRestriction.singleIso (algebraMap A B) (0 : ℤ)
                (ModuleCat.of B N)).inv⟦(1 : ℤ)⟧') := rfl

/-- If the displayed maps complete to a distinguished triangle, vanishing of the
connecting class characterizes the existence of a solution. -/
theorem exists_iff_connecting_eq_zero (c : KernelModule π →ₗ[A] N)
    (γ :
      -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
      letI := algebraOfSquareZero π
      Algebra.naiveCotangentObject A B ⟶ (underivedTensorObject π B)⟦(1 : ℤ)⟧)
    (hΔ :
      -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
      letI := algebraOfSquareZero π
      -- Local instance justification (noncanonical choice): Algebra A' B is determined by the composite of π with algebraMap A B.
      letI := algebraCompOfSquareZero π B
      -- Local instance justification (defeq pin): the tower A' → A → B is the composite of the algebra maps of π.
      letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
      Triangle.mk (baseChangeMapDerived π B) (sourceChangeMapDerived π B) γ ∈
        distTriang (DerivedCategory (ModuleCat B)))
    :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    Nonempty (IsoClass π B c) ↔
      ∃ f ξu,
        (
          -- Local instance justification (noncanonical choice): the representative uses the A'-algebra structure on A selected by the explicit π.
          letI := algebraOfSquareZero π
          extOneNaiveCotangent_mk A' A N f =
            extOneNaiveCotangent_map c (selfExtensionClass π)) ∧
        (
          -- Local instance justification (noncanonical choice): the Ext¹ comparison uses the A'-algebra structure on A selected by the explicit π.
          letI := algebraOfSquareZero π
          extOne_underived_precomp π B ξu = extOne_adjunction π B (toDerived π B f)) ∧
        (
          -- Local instance justification (noncanonical choice): uniqueness is stated in the Ext¹ group for the A'-algebra structure selected by the explicit π.
          letI := algebraOfSquareZero π
          ∀ ξu',
            extOne_underived_precomp π B ξu' = extOne_adjunction π B (toDerived π B f) →
              ξu' = ξu) ∧
        connectingExtTwo π B γ ξu = 0 := sorry

end RingHom.SquareZeroExtension
