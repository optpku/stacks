module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import ReasLib.Algebra.Homology.Embedding.Functor
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import ReasLib.CategoryTheory.Shift.ShiftedHom.Adjunction
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.BaseChange
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.BaseChange.Derived
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction.Single
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.ExtendScalars
public import stacks_project.Chap91.Lemma_91_2_7
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ext¹ identifications and Jacobi–Zariski maps in the square-zero setup

In the situation of Lemma 91.2.7, Ext¹ of `NL{A⁄A'}` is identified with Ext¹ of
the derived and underived base changes along `A → B`. The canonical maps
`NL{A⁄A'} ⊗[A] B ⟶ NL{B⁄A'} ⟶ NL{B⁄A}` are close to a distinguished triangle;
if they completed to one, the connecting image of ξ would obstruct solutions of
91.2.0.1.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory DerivedCategory HomologicalComplex ComplexShape
open CategoryTheory.Pretriangulated
open Algebra Algebra.Generators Algebra.Extension
open Algebra.Extension.NaiveCotangent
open Algebra.NaiveCotangent.DerivedBaseChange
open RingHom.SquareZeroExtension
open scoped DerivedExt NaiveCotangent DerivedTensorWithAlgebra

namespace RingHom.SquareZeroExtension

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

/-- The underlying equivalence of the derived extension-restriction identification of Ext¹. -/
def extOne_adjunction_equiv :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    Ext⁽(1 : ℤ)⁾(Algebra.naiveCotangentObject A' A,
        (ModuleCat.derivedRestrictionOfScalars (algebraMap A B)).obj
          ((singleFunctor (ModuleCat B) (0 : ℤ)).obj (ModuleCat.of B N))) ≃
      Ext⁽(1 : ℤ)⁾(Algebra.naiveCotangentObject A' A ⊗[A]^L[B],
        (singleFunctor (ModuleCat B) (0 : ℤ)).obj (ModuleCat.of B N)) :=
  -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
  letI := algebraOfSquareZero π
  (ModuleCat.derivedExtensionRestrictionAdjunction (algebraMap A B)).shiftedHomEquiv
    (Algebra.naiveCotangentObject A' A)
    ((singleFunctor (ModuleCat B) (0 : ℤ)).obj (ModuleCat.of B N))
    (1 : ℤ)

/-- The derived extension-restriction identification of Ext¹ is additive. -/
theorem extOne_adjunction_equiv_map_add
    (x y :
      -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
      letI := algebraOfSquareZero π
      Ext⁽(1 : ℤ)⁾(Algebra.naiveCotangentObject A' A,
        (ModuleCat.derivedRestrictionOfScalars (algebraMap A B)).obj
          ((singleFunctor (ModuleCat B) (0 : ℤ)).obj (ModuleCat.of B N)))) :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    extOne_adjunction_equiv π B (x + y) =
      extOne_adjunction_equiv π B x + extOne_adjunction_equiv π B y := sorry

/-- Remark 91.2.8 (1) In the situation of Lemma 91.2.7,
Ext¹_A(NL{A⁄A'}, N) = Ext¹_B(NL{A⁄A'} ⊗[A]^L[B], N) by More on Algebra, Lemma 15.60.3. -/
@[stacks 0GPY]
def extOne_adjunction :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    Ext⁽(1 : ℤ)⁾(Algebra.naiveCotangentObject A' A,
        (ModuleCat.derivedRestrictionOfScalars (algebraMap A B)).obj
          ((singleFunctor (ModuleCat B) (0 : ℤ)).obj (ModuleCat.of B N))) ≃+
      Ext⁽(1 : ℤ)⁾(Algebra.naiveCotangentObject A' A ⊗[A]^L[B],
        (singleFunctor (ModuleCat B) (0 : ℤ)).obj (ModuleCat.of B N)) :=
  -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
  letI := algebraOfSquareZero π
  AddEquiv.mk' (extOne_adjunction_equiv π B) (extOne_adjunction_equiv_map_add π B)

/-- The adjunction identification sends the zero class to zero. -/
theorem extOne_adjunction_apply :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    extOne_adjunction π B
      (0 : Ext⁽(1 : ℤ)⁾(Algebra.naiveCotangentObject A' A,
        (ModuleCat.derivedRestrictionOfScalars (algebraMap A B)).obj
          ((singleFunctor (ModuleCat B) (0 : ℤ)).obj (ModuleCat.of B N)))) = 0 := sorry

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

/-- Precomposition with `underivedComparison` sends the zero class to zero. -/
theorem extOne_underived_precomp_zero :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    extOne_underived_precomp π B
      (0 : Ext⁽(1 : ℤ)⁾(underivedTensorObject π B,
        (singleFunctor (ModuleCat B) (0 : ℤ)).obj (ModuleCat.of B N))) = 0 := sorry

/-- Remark 91.2.8 (2) The derived base-change Ext¹ equals Ext¹ of the underived
tensor `NL{A⁄A'} ⊗[A] B`, by More on Algebra, Lemma 15.86.1. -/
@[stacks 0GPY]
theorem extOne_underived :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    Function.Bijective
      (extOne_underived_precomp π B :
        Ext⁽(1 : ℤ)⁾(underivedTensorObject π B,
            (singleFunctor (ModuleCat B) (0 : ℤ)).obj (ModuleCat.of B N)) →
          Ext⁽(1 : ℤ)⁾(Algebra.naiveCotangentObject A' A ⊗[A]^L[B],
            (singleFunctor (ModuleCat B) (0 : ℤ)).obj (ModuleCat.of B N))) := sorry

/-- Remark 91.2.8 (3) The canonical map of complexes
`NL{A⁄A'} ⊗[A] B ⟶ NL{B⁄A'}` induced by the self-presentations. -/
@[stacks 0GPY]
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

/-- Remark 91.2.8 (4) The canonical map of complexes `NL{B⁄A'} ⟶ NL{B⁄A}` induced by
the self-presentations; together with `baseChangeMap` this is close to a distinguished
triangle, see Algebra, Lemma 10.134.4. -/
@[stacks 0GPY]
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

/-- The identity-on-carriers comparison between `N` as an `A`-module and the
restriction of scalars of `N` along `A → B`. -/
def restrictCoeffIso :
    ModuleCat.of A N ≅
      (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B N) :=
  (@AddEquiv.toLinearEquiv A N
      ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B N))
      _ _ _
      inferInstance
      ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B N)).isModule
      (AddEquiv.refl N) sorry).toModuleIso

/-- `restrictCoeffIso` is the identity on the underlying additive group of `N`. -/
theorem restrictCoeffIso_apply (x : ModuleCat.of A N) :
    (restrictCoeffIso B).hom x = x := sorry

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
              (Generators.self A' A).toExtension).toLinearMap) := sorry

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
        (extOne_cotangentHom_d_comp π f) := sorry

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
          (restrictCoeffIso B).hom)⟦(1 : ℤ)⟧') ≫
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
              (restrictCoeffIso B).hom)⟦(1 : ℤ)⟧') ≫
            ((ModuleCat.DerivedRestriction.singleIso (algebraMap A B) (0 : ℤ)
                (ModuleCat.of B N)).inv⟦(1 : ℤ)⟧') := sorry

/-- Remark 91.2.8 (5) If the maps of complexes completed to a distinguished triangle via
an explicit connecting morphism `γ`, then a solution of 91.2.0.1 exists if and only if
the connecting image of ξ in Ext⁽2⁾_B(NL{B⁄A}, N) vanishes. Here ξ is the image of a
Hom representative of `extOneNaiveCotangent_map c (selfExtensionClass π)` under
`toDerived`, transported along `extOne_adjunction`, and uniquely lifted through
`extOne_underived_precomp`. -/
@[stacks 0GPY]
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
    (f :
      -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
      letI := algebraOfSquareZero π
      (Generators.self A' A).toExtension.Cotangent →ₗ[A] N)
    (hf :
      -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
      letI := algebraOfSquareZero π
      extOneNaiveCotangent_mk A' A N f =
        extOneNaiveCotangent_map c (selfExtensionClass π))
    (ξu :
      -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
      letI := algebraOfSquareZero π
      Ext⁽(1 : ℤ)⁾(underivedTensorObject π B,
        (singleFunctor (ModuleCat B) (0 : ℤ)).obj (ModuleCat.of B N)))
    (hξu :
      -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
      letI := algebraOfSquareZero π
      extOne_underived_precomp π B ξu = extOne_adjunction π B (toDerived π B f))
    (hξu_unique :
      -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
      letI := algebraOfSquareZero π
      ∀ ξu',
        extOne_underived_precomp π B ξu' = extOne_adjunction π B (toDerived π B f) →
          ξu' = ξu) :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    Nonempty (IsoClass π B c) ↔
      connectingExtTwo π B γ ξu = 0 := sorry

end SquareZeroExtension

end RingHom
