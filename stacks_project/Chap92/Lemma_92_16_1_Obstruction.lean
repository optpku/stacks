module

public import Mathlib.Algebra.Category.ModuleCat.LeftResolution
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.Embedding.Extend
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Adjunction
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import ReasLib.CategoryTheory.Shift.ShiftedHom.Equiv
public import stacks_project.Chap91.Lemma_91_2_1_Diagram
public import stacks_project.Chap91.Lemma_91_2_2
public import stacks_project.Chap91.Remark_91_2_8
public import stacks_project.Chap92.Lemma_92_4_5
public import stacks_project.Chap92.Lemma_92_16_1_Comparison

/-!
# Cotangent Ext² existence obstruction of a square-zero deformation

A square-zero surjection π : A' →+* A, an A-algebra B, a B-module N, and an
A-linear map c : ker π → N determine a canonical class in
Ext⁽2⁾(Algebra.CotangentComplex.derived A B, N[0]). The class is the connecting
image of the tautological Ext¹ class of L_{A/A'} ⊗^L_A B along the
transitivity triangle of A' → A → B.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory DerivedCategory HomologicalComplex ComplexShape
open CategoryTheory.Limits
open DerivedCategory.TStructure
open Algebra Algebra.Generators Algebra.Extension
open Algebra.CotangentComplex
open Algebra.NaiveCotangent
open CommRingCat.Under.CotangentComplex
open CommRingCat.Under.FreeAlgebra
open RingHom.SquareZeroExtension
open scoped DerivedExt DerivedTensorWithAlgebra NaiveCotangent

namespace RingHom.SquareZeroExtension

variable {A' A : Type u} [CommRing A'] [CommRing A]
variable (π : A' →+* A) [π.IsSquareZeroExtension]
variable (B : Type u) [CommRing B] [Algebra A B]
variable {N : Type u} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]

/-- The coefficient object `N[0]` in `D(Mod B)`. -/
abbrev coeffSingle (N : Type u) [AddCommGroup N] [Module B N] :
    DerivedCategory (ModuleCat.{u} B) :=
  (singleFunctor (ModuleCat.{u} B) (0 : ℤ)).obj (ModuleCat.of B N)

/-- Unfolding of `coeffSingle` as the degree-zero single object on `N`. -/
theorem coeffSingle_eq (N : Type u) [AddCommGroup N] [Module B N] :
    coeffSingle B N =
      (singleFunctor (ModuleCat.{u} B) (0 : ℤ)).obj (ModuleCat.of B N) :=
  sorry

/-- The derived Ext¹ class of a Hom representative of `extOneNaiveCotangent A' A N`,
aligned with restriction of scalars of `N[0]` along `A → B`. -/
def toDerivedClass
    (ξ :
      -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
      letI := algebraOfSquareZero π
      extOneNaiveCotangent A' A N) :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    Ext⁽(1 : ℤ)⁾(Algebra.naiveCotangentObject A' A,
      (ModuleCat.derivedRestrictionOfScalars (algebraMap A B)).obj (coeffSingle B N)) :=
  -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
  letI := algebraOfSquareZero π
  Quotient.liftOn ξ (fun f ↦ toDerived π B f) sorry

/-- `toDerivedClass` on a Hom representative is `toDerived`. -/
theorem toDerivedClass_mk
    (f :
      -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
      letI := algebraOfSquareZero π
      (Generators.self A' A).toExtension.Cotangent →ₗ[A] N) :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    toDerivedClass π B (extOneNaiveCotangent_mk A' A N f) = toDerived π B f :=
  sorry

/-- The Ext¹ class of `NL{A⁄A'} ⊗[A]^L[B]` obtained by adjunction from the tautological
square-zero class of π, pushed along `c`. -/
def xiPrimeNaive (c : KernelModule π →ₗ[A] N) :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    Ext⁽(1 : ℤ)⁾(Algebra.naiveCotangentObject A' A ⊗[A]^L[B], coeffSingle B N) :=
  -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
  letI := algebraOfSquareZero π
  extOne_adjunction π B
    (toDerivedClass π B (extOneNaiveCotangent_map c (selfExtensionClass π)))

/-- `xiPrimeNaive` is `extOne_adjunction` of `toDerivedClass` of the image of
`selfExtensionClass π` along `c`. -/
theorem xiPrimeNaive_eq (c : KernelModule π →ₗ[A] N) :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    xiPrimeNaive π B c =
      extOne_adjunction π B
        (toDerivedClass π B (extOneNaiveCotangent_map c (selfExtensionClass π))) :=
  sorry

/-- The Ext¹ class of the cochain-level scalar extension of `NL{A⁄A'}`, obtained by
termwise `extendScalars` of a Hom representative. -/
def toCochainExt
    (f :
      -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
      letI := algebraOfSquareZero π
      (Generators.self A' A).toExtension.Cotangent →ₗ[A] N) :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    -- Local instance justification (noncanonical choice): Algebra A' B is determined by the composite of π with algebraMap A B.
    letI := algebraCompOfSquareZero π B
    -- Local instance justification (defeq pin): the tower A' → A → B is the composite of the algebra maps of π.
    letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
    Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj
        (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)).obj
          (selfNaiveComplex (CommRingCat.of A') (under A' A))),
        coeffSingle B N) :=
  -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
  letI := algebraOfSquareZero π
  -- Local instance justification (noncanonical choice): Algebra A' B is determined by the composite of π with algebraMap A B.
  letI := algebraCompOfSquareZero π B
  -- Local instance justification (defeq pin): the tower A' → A → B is the composite of the algebra maps of π.
  letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
  DerivedCategory.Q.map
      (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)).map
        (extendMap (extOneHomUnderChain A' A f) embeddingDownNat)) ≫
    DerivedCategory.Q.map
      (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)).map
        (extendSingleIso embeddingDownNat (ModuleCat.of A N) 1 (-1 : ℤ) rfl).hom) ≫
    DerivedCategory.Q.map
      ((singleMapHomologicalComplex
          (ModuleCat.extendScalars (algebraMap A B)) (up ℤ) (-1 : ℤ)).hom.app
        (ModuleCat.of A N)) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.single (ModuleCat.{u} B) (up ℤ) (-1 : ℤ)).map
        ((ModuleCat.extendScalars (algebraMap A B)).map (restrictCoeffIso B).hom ≫
          (ModuleCat.extendRestrictScalarsAdj (algebraMap A B)).counit.app
            (ModuleCat.of B N))) ≫
    ((DerivedCategory.singleFunctors (ModuleCat.{u} B)).shiftIso (1 : ℤ) (-1) 0
        (add_neg_cancel (1 : ℤ))).inv.app (ModuleCat.of B N)

/-- `toCochainExt` on a Hom representative of the pushed tautological class. -/
theorem toCochainExt_eq
    (f :
      -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
      letI := algebraOfSquareZero π
      (Generators.self A' A).toExtension.Cotangent →ₗ[A] N) :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    -- Local instance justification (noncanonical choice): Algebra A' B is determined by the composite of π with algebraMap A B.
    letI := algebraCompOfSquareZero π B
    -- Local instance justification (defeq pin): the tower A' → A → B is the composite of the algebra maps of π.
    letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
    toCochainExt π B f =
      DerivedCategory.Q.map
          (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)).map
            (extendMap (extOneHomUnderChain A' A f) embeddingDownNat)) ≫
        DerivedCategory.Q.map
          (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)).map
            (extendSingleIso embeddingDownNat (ModuleCat.of A N) 1 (-1 : ℤ) rfl).hom) ≫
        DerivedCategory.Q.map
          ((singleMapHomologicalComplex
              (ModuleCat.extendScalars (algebraMap A B)) (up ℤ) (-1 : ℤ)).hom.app
            (ModuleCat.of A N)) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.single (ModuleCat.{u} B) (up ℤ) (-1 : ℤ)).map
            ((ModuleCat.extendScalars (algebraMap A B)).map (restrictCoeffIso B).hom ≫
              (ModuleCat.extendRestrictScalarsAdj (algebraMap A B)).counit.app
                (ModuleCat.of B N))) ≫
        ((DerivedCategory.singleFunctors (ModuleCat.{u} B)).shiftIso (1 : ℤ) (-1) 0
            (add_neg_cancel (1 : ℤ))).inv.app (ModuleCat.of B N) :=
  sorry

/-- The Ext¹ class of the cochain-level scalar extension of `NL{A⁄A'}`, lifted from an
`extOneNaiveCotangent` class. -/
def toCochainClass
    (ξ :
      -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
      letI := algebraOfSquareZero π
      extOneNaiveCotangent A' A N) :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    -- Local instance justification (noncanonical choice): Algebra A' B is determined by the composite of π with algebraMap A B.
    letI := algebraCompOfSquareZero π B
    -- Local instance justification (defeq pin): the tower A' → A → B is the composite of the algebra maps of π.
    letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
    Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj
        (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)).obj
          (selfNaiveComplex (CommRingCat.of A') (under A' A))),
        coeffSingle B N) :=
  -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
  letI := algebraOfSquareZero π
  -- Local instance justification (noncanonical choice): Algebra A' B is determined by the composite of π with algebraMap A B.
  letI := algebraCompOfSquareZero π B
  -- Local instance justification (defeq pin): the tower A' → A → B is the composite of the algebra maps of π.
  letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
  Quotient.liftOn ξ (fun f ↦ toCochainExt π B f) sorry

/-- `toCochainClass` on a Hom representative is `toCochainExt`. -/
theorem toCochainClass_mk
    (f :
      -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
      letI := algebraOfSquareZero π
      (Generators.self A' A).toExtension.Cotangent →ₗ[A] N) :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    -- Local instance justification (noncanonical choice): Algebra A' B is determined by the composite of π with algebraMap A B.
    letI := algebraCompOfSquareZero π B
    -- Local instance justification (defeq pin): the tower A' → A → B is the composite of the algebra maps of π.
    letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
    toCochainClass π B (extOneNaiveCotangent_mk A' A N f) = toCochainExt π B f :=
  sorry

/-- The cochain-level scalar extension of `NL{A⁄A'}` of the pushed tautological class. -/
def xiPrimeCochain (c : KernelModule π →ₗ[A] N) :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    -- Local instance justification (noncanonical choice): Algebra A' B is determined by the composite of π with algebraMap A B.
    letI := algebraCompOfSquareZero π B
    -- Local instance justification (defeq pin): the tower A' → A → B is the composite of the algebra maps of π.
    letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
    Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj
        (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)).obj
          (selfNaiveComplex (CommRingCat.of A') (under A' A))),
        coeffSingle B N) :=
  -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
  letI := algebraOfSquareZero π
  -- Local instance justification (noncanonical choice): Algebra A' B is determined by the composite of π with algebraMap A B.
  letI := algebraCompOfSquareZero π B
  -- Local instance justification (defeq pin): the tower A' → A → B is the composite of the algebra maps of π.
  letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
  toCochainClass π B (extOneNaiveCotangent_map c (selfExtensionClass π))

/-- `xiPrimeCochain` is `toCochainClass` of the image of `selfExtensionClass π` along `c`. -/
theorem xiPrimeCochain_eq (c : KernelModule π →ₗ[A] N) :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    -- Local instance justification (noncanonical choice): Algebra A' B is determined by the composite of π with algebraMap A B.
    letI := algebraCompOfSquareZero π B
    -- Local instance justification (defeq pin): the tower A' → A → B is the composite of the algebra maps of π.
    letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
    xiPrimeCochain π B c =
      toCochainClass π B (extOneNaiveCotangent_map c (selfExtensionClass π)) :=
  sorry

/-- The canonical Ext¹ class ξ' of `L_{A/A'} ⊗^L_A B`, as precomposition of `xiPrimeCochain`
along the real cochain comparison `tensorToNaiveTensor`. -/
def xiPrime (c : KernelModule π →ₗ[A] N) :=
  -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
  letI := algebraOfSquareZero π
  -- Local instance justification (noncanonical choice): Algebra A' B is determined by the composite of π with algebraMap A B.
  letI := algebraCompOfSquareZero π B
  -- Local instance justification (defeq pin): the tower A' → A → B is the composite of the algebra maps of π.
  letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
  (ShiftedHom.comp (ShiftedHom.mk₀ (0 : ℤ) rfl (tensorToNaiveTensor A' A B))
    (xiPrimeCochain π B c) (add_zero (1 : ℤ)) :
    Ext⁽(1 : ℤ)⁾(tensor A' A B, coeffSingle B N))

/-- `existenceObstruction` is assembled from `connectingMap` and `xiPrime`. -/
def existenceObstruction (c : KernelModule π →ₗ[A] N) :
    Ext⁽(2 : ℤ)⁾(derived A B, coeffSingle B N) :=
  -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
  letI := algebraOfSquareZero π
  -- Local instance justification (noncanonical choice): Algebra A' B is determined by the composite of π with algebraMap A B.
  letI := algebraCompOfSquareZero π B
  -- Local instance justification (defeq pin): the tower A' → A → B is the composite of the algebra maps of π.
  letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
  ShiftedHom.comp (connectingMap A' A B) (xiPrime π B c) rfl

/-- `existenceObstruction` is `ShiftedHom.comp` of `connectingMap A' A B` with `xiPrime`. -/
theorem existenceObstruction_eq (c : KernelModule π →ₗ[A] N) :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    -- Local instance justification (noncanonical choice): Algebra A' B is determined by the composite of π with algebraMap A B.
    letI := algebraCompOfSquareZero π B
    -- Local instance justification (defeq pin): the tower A' → A → B is the composite of the algebra maps of π.
    letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
    existenceObstruction π B c =
      ShiftedHom.comp (connectingMap A' A B) (xiPrime π B c) rfl :=
  sorry

/-- `xiPrimeNaive` is the adjunction/`toDerivedClass` image of
`extOneNaiveCotangent_map c (selfExtensionClass π)`. -/
theorem existenceObstruction_spec (c : KernelModule π →ₗ[A] N) :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    xiPrimeNaive π B c =
      extOne_adjunction π B
        (toDerivedClass π B (extOneNaiveCotangent_map c (selfExtensionClass π))) :=
  sorry

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable (N : Type u) [AddCommGroup N] [Module B N]

/-- The derived morphism `L_{B/A} ⟶ NL_{B/A}` of the self-presentation. -/
def derivedToSelfNaive :
    derived A B ⟶
      DerivedCategory.Q.obj (selfNaiveComplex (CommRingCat.of A) (under A B)) :=
  derivedToNaiveObject A B

/-- Unfolding of `derivedToSelfNaive` as `derivedToNaiveObject`. -/
theorem derivedToSelfNaive_eq :
    derivedToSelfNaive A B = derivedToNaiveObject A B :=
  sorry

/-- The chain map `NL{B⁄A} ⟶ N[1]` attached to a Hom representative. -/
def extOneHomSelf (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
    naiveChain (CommRingCat.of A) (under A B) (under A B).right
        (selfHom (CommRingCat.of A) (under A B)) ⟶
      (HomologicalComplex.single (ModuleCat B) (ComplexShape.down ℕ) 1).obj
        (ModuleCat.of B N) :=
  extOneHomUnderChain A B f

/-- The derived Ext¹ class of a Hom representative on `NL_{B/A}`. -/
def toNaiveExt (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
    Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj
        (selfNaiveComplex (CommRingCat.of A) (under A B)), coeffSingle B N) :=
  DerivedCategory.Q.map
      (extendMap (extOneHomSelf A B N f) embeddingDownNat) ≫
    DerivedCategory.Q.map
      (extendSingleIso embeddingDownNat (ModuleCat.of B N) 1 (-1 : ℤ) rfl).hom ≫
    ((DerivedCategory.singleFunctors (ModuleCat B)).shiftIso (1 : ℤ) (-1) 0
        (add_neg_cancel (1 : ℤ))).inv.app (ModuleCat.of B N)

/-- The Ext¹ class of `L_{B/A}` attached to a Hom representative, by precomposition
with `derivedToSelfNaive`. -/
def toDerivedExt
    (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
    Ext⁽(1 : ℤ)⁾(derived A B, coeffSingle B N) :=
  ShiftedHom.comp (ShiftedHom.mk₀ (0 : ℤ) rfl (derivedToSelfNaive A B))
    (toNaiveExt A B N f) (add_zero (1 : ℤ))

/-- The shifted coefficient object `N[1]` lies in `t.GE (-1)`. -/
instance coeffSingle_shift_isGE :
    t.IsGE ((coeffSingle B N)⟦(1 : ℤ)⟧) (-1) :=
  t.isGE_shift (coeffSingle B N) (0 : ℤ) (1 : ℤ) (-1)

/-- The Ext¹ class of `NL_{B/A}` obtained from a derived Ext¹ class by precomposition
with `naiveTruncGESection` and the t-structure section of `N[1]`. -/
def fromDerivedToNaiveExt
    (η : Ext⁽(1 : ℤ)⁾(derived A B, coeffSingle B N)) :
    Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj
        (selfNaiveComplex (CommRingCat.of A) (under A B)), coeffSingle B N) :=
  -- Local instance justification (defeq pin): N[0] is GE 0, so N[0]⟦1⟧ is GE -1 and truncGEπ is invertible on that object.
  letI : t.IsGE ((coeffSingle B N)⟦(1 : ℤ)⟧) (-1) :=
    t.isGE_shift (coeffSingle B N) (0 : ℤ) (1 : ℤ) (-1)
  ShiftedHom.comp (ShiftedHom.mk₀ (0 : ℤ) rfl (naiveTruncGESection A B))
    (t.descTruncGE (η : derived A B ⟶ (coeffSingle B N)⟦(1 : ℤ)⟧) (-1))
    (add_zero (1 : ℤ))

/-- The cochain-complex single object `N[0]`. -/
abbrev coeffCochain (N : Type u) [AddCommGroup N] [Module B N] :
    CochainComplex (ModuleCat.{u} B) ℤ :=
  (CochainComplex.singleFunctor (ModuleCat.{u} B) (0 : ℤ)).obj (ModuleCat.of B N)

/-- Unfolding of `coeffCochain` as the cochain-complex single object on `N`. -/
theorem coeffCochain_eq (N : Type u) [AddCommGroup N] [Module B N] :
    coeffCochain B N =
      (CochainComplex.singleFunctor (ModuleCat.{u} B) (0 : ℤ)).obj (ModuleCat.of B N) :=
  sorry

/-- Free `B`-module on the underlying type of the Under self-presentation conormal. -/
abbrev selfNaiveConormalFree (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    ModuleCat.{u} B :=
  (ModuleCat.free B).obj
    ((CategoryTheory.forget (ModuleCat.{u} B)).obj
      (naiveConormal (CommRingCat.of A) (under A B) (under A B).right
        (selfHom (CommRingCat.of A) (under A B))))

/-- Unfolding of `selfNaiveConormalFree` as the free module on the conormal. -/
theorem selfNaiveConormalFree_eq :
    selfNaiveConormalFree A B =
      (ModuleCat.free B).obj
        ((CategoryTheory.forget (ModuleCat.{u} B)).obj
          (naiveConormal (CommRingCat.of A) (under A B) (under A B).right
            (selfHom (CommRingCat.of A) (under A B)))) :=
  sorry

/-- Canonical termwise surjection from the free module on the conormal. -/
def selfNaiveConormalFreeπ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    selfNaiveConormalFree A B ⟶
      naiveConormal (CommRingCat.of A) (under A B) (under A B).right
        (selfHom (CommRingCat.of A) (under A B)) :=
  (ModuleCat.adj B).counit.app
    (naiveConormal (CommRingCat.of A) (under A B) (under A B).right
      (selfHom (CommRingCat.of A) (under A B)))

/-- `selfNaiveConormalFreeπ` is the free-forgetful counit on the conormal. -/
theorem selfNaiveConormalFreeπ_eq :
    selfNaiveConormalFreeπ A B =
      (ModuleCat.adj B).counit.app
        (naiveConormal (CommRingCat.of A) (under A B) (under A B).right
          (selfHom (CommRingCat.of A) (under A B))) :=
  sorry

/-- Underlying generating type of the almost-free replacement in homological degree `n`. -/
def selfNaiveAlmostFreeCarrier (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (n : ℕ) : Type u :=
  match n with
  | 0 =>
      (CategoryTheory.forget (ModuleCat.{u} B)).obj
        (naiveDifferentials (CommRingCat.of A) (under A B) (under A B).right
          (selfHom (CommRingCat.of A) (under A B)))
  | 1 =>
      (CategoryTheory.forget (ModuleCat.{u} B)).obj
        (naiveConormal (CommRingCat.of A) (under A B) (under A B).right
          (selfHom (CommRingCat.of A) (under A B)))
  | 2 => (CategoryTheory.forget (ModuleCat.{u} B)).obj (kernel (selfNaiveConormalFreeπ A B))
  | _ + 3 => PEmpty.{u + 1}

/-- Degree `1` of `selfNaiveAlmostFreeCarrier` is the underlying type of the conormal. -/
theorem selfNaiveAlmostFreeCarrier_one :
    selfNaiveAlmostFreeCarrier A B 1 =
      (CategoryTheory.forget (ModuleCat.{u} B)).obj
        (naiveConormal (CommRingCat.of A) (under A B) (under A B).right
          (selfHom (CommRingCat.of A) (under A B))) :=
  sorry

/-- Degree-`n` term of the almost-free replacement, free on the generating type. -/
abbrev selfNaiveAlmostFreeX (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (n : ℕ) : ModuleCat.{u} B :=
  (ModuleCat.free B).obj (selfNaiveAlmostFreeCarrier A B n)

/-- Unfolding of `selfNaiveAlmostFreeX` as a free module on the generating type. -/
theorem selfNaiveAlmostFreeX_eq (n : ℕ) :
    selfNaiveAlmostFreeX A B n =
      (ModuleCat.free B).obj (selfNaiveAlmostFreeCarrier A B n) :=
  sorry

/-- Each term of the almost-free replacement is a free, hence projective, `B`-module. -/
instance selfNaiveAlmostFreeX_projective (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (n : ℕ) :
    CategoryTheory.Projective (selfNaiveAlmostFreeX A B n) :=
  inferInstance

/-- Differentials of the almost-free replacement. Degree `0` is the free functor applied
to the underlying map of `naiveDifferential`; degree `1` is the free cover of
`ker (selfNaiveConormalFreeπ)`. -/
def selfNaiveAlmostFree_d (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (n : ℕ) :
    selfNaiveAlmostFreeX A B (n + 1) ⟶ selfNaiveAlmostFreeX A B n :=
  match n with
  | 0 =>
      (ModuleCat.free B).map
        ((CategoryTheory.forget (ModuleCat.{u} B)).map
          (naiveDifferential (CommRingCat.of A) (under A B) (under A B).right
            (selfHom (CommRingCat.of A) (under A B))))
  | 1 =>
      (ModuleCat.adj B).counit.app (kernel (selfNaiveConormalFreeπ A B)) ≫
        kernel.ι (selfNaiveConormalFreeπ A B)
  | _ + 2 => 0

/-- Unfolding of the degree-`0` almost-free differential as the free functor applied
to the underlying map of `naiveDifferential`. -/
theorem selfNaiveAlmostFree_d_zero :
    selfNaiveAlmostFree_d A B 0 =
      (ModuleCat.free B).map
        ((CategoryTheory.forget (ModuleCat.{u} B)).map
          (naiveDifferential (CommRingCat.of A) (under A B) (under A B).right
            (selfHom (CommRingCat.of A) (under A B)))) :=
  sorry

/-- Bounded-above almost-free chain complex of the Under self-presentation, with free
terms on the differentials, the conormal, and the kernel of the conormal cover. -/
def selfNaiveAlmostFreeChain (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    ChainComplex (ModuleCat.{u} B) ℕ :=
  ChainComplex.of (selfNaiveAlmostFreeX A B) (selfNaiveAlmostFree_d A B) (fun _ ↦ sorry)

/-- Degree `0` of `selfNaiveAlmostFreeChain` is the free cover of the differentials. -/
theorem selfNaiveAlmostFreeChain_X_zero :
    (selfNaiveAlmostFreeChain A B).X 0 = selfNaiveAlmostFreeX A B 0 :=
  sorry

/-- Each homological degree of `selfNaiveAlmostFreeChain` is projective. -/
instance selfNaiveAlmostFreeChain_projective (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (n : ℕ) :
    CategoryTheory.Projective ((selfNaiveAlmostFreeChain A B).X n) :=
  selfNaiveAlmostFreeX_projective A B n

/-- Cochain-complex extension of the almost-free replacement, concentrated in degrees `≤ 0`. -/
abbrev selfNaiveAlmostFreeComplex (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    CochainComplex (ModuleCat.{u} B) ℤ :=
  (selfNaiveAlmostFreeChain A B).extend ComplexShape.embeddingDownNat

/-- Unfolding of `selfNaiveAlmostFreeComplex` as the `embeddingDownNat` extension. -/
theorem selfNaiveAlmostFreeComplex_eq :
    selfNaiveAlmostFreeComplex A B =
      (selfNaiveAlmostFreeChain A B).extend ComplexShape.embeddingDownNat :=
  sorry

/-- The almost-free replacement is K-projective, as a bounded-above complex of projectives. -/
instance selfNaiveAlmostFreeComplex_isKProjective (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    (selfNaiveAlmostFreeComplex A B).IsKProjective :=
  inferInstance

/-- Components of the termwise surjection from the almost-free replacement onto the
Under naive chain complex. -/
def selfNaiveAlmostFreeπChain_f (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (n : ℕ) :
    (selfNaiveAlmostFreeChain A B).X n ⟶
      (naiveChain (CommRingCat.of A) (under A B) (under A B).right
        (selfHom (CommRingCat.of A) (under A B))).X n :=
  match n with
  | 0 =>
      (ModuleCat.adj B).counit.app
        (naiveDifferentials (CommRingCat.of A) (under A B) (under A B).right
          (selfHom (CommRingCat.of A) (under A B)))
  | 1 => selfNaiveConormalFreeπ A B
  | _ + 2 => 0

/-- Degree `1` of `selfNaiveAlmostFreeπChain_f` is `selfNaiveConormalFreeπ`. -/
theorem selfNaiveAlmostFreeπChain_f_eq_one :
    selfNaiveAlmostFreeπChain_f A B 1 = selfNaiveConormalFreeπ A B :=
  sorry

/-- Termwise surjection of chain complexes from the almost-free replacement onto
the Under naive cotangent chain. -/
def selfNaiveAlmostFreeπChain (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    selfNaiveAlmostFreeChain A B ⟶
      naiveChain (CommRingCat.of A) (under A B) (under A B).right
        (selfHom (CommRingCat.of A) (under A B)) :=
  ChainComplex.ofHom (selfNaiveAlmostFreeπChain_f A B) (fun _ ↦ sorry)

/-- Degree `1` of `selfNaiveAlmostFreeπChain` is `selfNaiveConormalFreeπ`. -/
theorem selfNaiveAlmostFreeπChain_f_one :
    (selfNaiveAlmostFreeπChain A B).f 1 = selfNaiveConormalFreeπ A B :=
  sorry

/-- Termwise surjection `F^• ⟶ NL_{B/A}` of the almost-free replacement onto the
Under self-presentation naive cotangent complex. -/
def selfNaiveAlmostFreeπ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    selfNaiveAlmostFreeComplex A B ⟶
      selfNaiveComplex (CommRingCat.of A) (under A B) :=
  HomologicalComplex.extendMap (selfNaiveAlmostFreeπChain A B) ComplexShape.embeddingDownNat

/-- Unfolding of `selfNaiveAlmostFreeπ` as `extendMap` of the chain-level surjection. -/
theorem selfNaiveAlmostFreeπ_eq :
    selfNaiveAlmostFreeπ A B =
      HomologicalComplex.extendMap (selfNaiveAlmostFreeπChain A B)
        ComplexShape.embeddingDownNat :=
  sorry

/-- The chain map `F^• ⟶ N[1]` representing a derived Ext¹ class, obtained by inverting
localization on the K-projective almost-free replacement. -/
def extOneChainOfAlmostFree
    (η : Ext⁽(1 : ℤ)⁾(derived A B, coeffSingle B N)) :
    selfNaiveAlmostFreeComplex A B ⟶ (coeffCochain B N)⟦(1 : ℤ)⟧ :=
  ((Equiv.ofBijective
      (DerivedCategory.Qh.map :
        ((HomotopyCategory.quotient (ModuleCat.{u} B) (up ℤ)).obj
            (selfNaiveAlmostFreeComplex A B) ⟶
          (HomotopyCategory.quotient (ModuleCat.{u} B) (up ℤ)).obj
            ((coeffCochain B N)⟦(1 : ℤ)⟧)) →
        (DerivedCategory.Q.obj (selfNaiveAlmostFreeComplex A B) ⟶
          DerivedCategory.Q.obj ((coeffCochain B N)⟦(1 : ℤ)⟧)))
      (CochainComplex.IsKProjective.Qh_map_bijective
        (selfNaiveAlmostFreeComplex A B)
        ((HomotopyCategory.quotient (ModuleCat.{u} B) (up ℤ)).obj
          ((coeffCochain B N)⟦(1 : ℤ)⟧)))).symm
    (DerivedCategory.Q.map (selfNaiveAlmostFreeπ A B) ≫
      fromDerivedToNaiveExt A B N η ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app (coeffCochain B N))).out

/-- `Q.map` of `extOneChainOfAlmostFree` recovers the precomposition of the truncation-section
Ext¹ class along `selfNaiveAlmostFreeπ`. -/
theorem extOneChainOfAlmostFree_comp_Q
    (η : Ext⁽(1 : ℤ)⁾(derived A B, coeffSingle B N)) :
    DerivedCategory.Q.map (extOneChainOfAlmostFree A B N η) =
      DerivedCategory.Q.map (selfNaiveAlmostFreeπ A B) ≫
        fromDerivedToNaiveExt A B N η ≫
          (DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app (coeffCochain B N) :=
  sorry

/-- Descent of a map out of the free module on the conormal along the termwise surjection,
forced by vanishing of `N[1]` in degrees `≤ -2`. -/
def descendConormalFree
    (f : selfNaiveAlmostFreeX A B 1 ⟶ ((coeffCochain B N)⟦(1 : ℤ)⟧).X (-1)) :
    naiveConormal (CommRingCat.of A) (under A B) (under A B).right
        (selfHom (CommRingCat.of A) (under A B)) ⟶
      ((coeffCochain B N)⟦(1 : ℤ)⟧).X (-1) :=
  ConcreteCategory.ofHom
    { toFun := fun x ↦ f (ModuleCat.freeMk x)
      map_add' := sorry
      map_smul' := sorry }

/-- Evaluation of `descendConormalFree` on a generator is the original map on `freeMk`. -/
theorem descendConormalFree_apply
    (f : selfNaiveAlmostFreeX A B 1 ⟶ ((coeffCochain B N)⟦(1 : ℤ)⟧).X (-1))
    (x :
      (CategoryTheory.forget (ModuleCat.{u} B)).obj
        (naiveConormal (CommRingCat.of A) (under A B) (under A B).right
          (selfHom (CommRingCat.of A) (under A B)))) :
    descendConormalFree A B N f x = f (ModuleCat.freeMk x) :=
  sorry

/-- Degreewise components of the representing chain map `NL_{B/A} ⟶ N[1]`, obtained by
factoring the almost-free chain map through the termwise surjection. -/
def extOneChainOfDerived_f
    (η : Ext⁽(1 : ℤ)⁾(derived A B, coeffSingle B N)) :
    ∀ i : ℤ,
      (selfNaiveComplex (CommRingCat.of A) (under A B)).X i ⟶
        ((coeffCochain B N)⟦(1 : ℤ)⟧).X i
  | -1 =>
      (naiveComplex_X_negOne (CommRingCat.of A) (under A B) (under A B).right
          (selfHom (CommRingCat.of A) (under A B))).hom ≫
        descendConormalFree A B N
          (((selfNaiveAlmostFreeChain A B).extendXIso ComplexShape.embeddingDownNat
              (rfl : ComplexShape.embeddingDownNat.f 1 = -1)).inv ≫
            (extOneChainOfAlmostFree A B N η).f (-1))
  | _ => 0

/-- The degree `-1` component of `extOneChainOfDerived_f` is the descended
almost-free chain map. -/
theorem extOneChainOfDerived_f_negOne
    (η : Ext⁽(1 : ℤ)⁾(derived A B, coeffSingle B N)) :
    extOneChainOfDerived_f A B N η (-1) =
      (naiveComplex_X_negOne (CommRingCat.of A) (under A B) (under A B).right
          (selfHom (CommRingCat.of A) (under A B))).hom ≫
        descendConormalFree A B N
          (((selfNaiveAlmostFreeChain A B).extendXIso ComplexShape.embeddingDownNat
              (rfl : ComplexShape.embeddingDownNat.f 1 = -1)).inv ≫
            (extOneChainOfAlmostFree A B N η).f (-1)) :=
  sorry

/-- The chain map `NL_{B/A} ⟶ N[1]` representing a derived Ext¹ class, obtained by
factoring the almost-free representative through the termwise surjection, using that
`N[1]` vanishes in degrees `≤ -2`. -/
def extOneChainOfDerived
    (η : Ext⁽(1 : ℤ)⁾(derived A B, coeffSingle B N)) :
    selfNaiveComplex (CommRingCat.of A) (under A B) ⟶ (coeffCochain B N)⟦(1 : ℤ)⟧ where
  f := extOneChainOfDerived_f A B N η
  comm' := sorry

/-- `Q.map` of `extOneChainOfDerived` recovers the truncation-section Ext¹ class,
transported along `Q.commShiftIso`. -/
theorem extOneChainOfDerived_comp_Q
    (η : Ext⁽(1 : ℤ)⁾(derived A B, coeffSingle B N)) :
    DerivedCategory.Q.map (extOneChainOfDerived A B N η) =
      fromDerivedToNaiveExt A B N η ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app (coeffCochain B N) :=
  sorry

/-- The Hom representative of a derived Ext¹ class, obtained from the degree `-1`
component of the chain map `NL_{B/A} ⟶ N[1]` and the Under-vs-Generators.self
conormal comparison. -/
def homOfExtOne
    (η : Ext⁽(1 : ℤ)⁾(derived A B, coeffSingle B N)) :
    (Generators.self A B).toExtension.Cotangent →ₗ[B] N :=
  (selfNaiveConormalInv A B ≫
    (naiveComplex_X_negOne (CommRingCat.of A) (under A B) (under A B).right
        (selfHom (CommRingCat.of A) (under A B))).inv ≫
    (extOneChainOfDerived A B N η).f (-1) ≫
    (singleObjXSelf (up ℤ) (0 : ℤ) (ModuleCat.of B N)).hom).hom

/-- The naive-to-derived Ext¹ comparison of `NL_{B/A}` with `L_{B/A}`. -/
def extOneNaiveDerivedEquiv :
    extOneNaiveCotangent A B N ≃+ Ext⁽(1 : ℤ)⁾(derived A B, coeffSingle B N) where
  toFun ξ := Quotient.liftOn ξ (fun f ↦ toDerivedExt A B N f) sorry
  invFun η := extOneNaiveCotangent_mk A B N (homOfExtOne A B N η)
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry

/-- The forward map of `extOneNaiveDerivedEquiv` on a Hom representative is `toDerivedExt`. -/
theorem extOneNaiveDerivedEquiv_mk
    (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
    extOneNaiveDerivedEquiv A B N (extOneNaiveCotangent_mk A B N f) =
      toDerivedExt A B N f :=
  sorry

/-- The unshifted morphism `L_{B/A} ⟶ N[0]` attached to a B-linear map out of `Ω[B⁄A]`. -/
def homKaehlerDerived (α : Ω[B⁄A] →ₗ[B] N) :
    derived A B ⟶ coeffSingle B N :=
  DerivedCategory.Q.map (augmentation A B) ≫
    (singleFunctorIsoCompQ (ModuleCat.{u} B) (0 : ℤ)).inv.app (ModuleCat.of B Ω[B⁄A]) ≫
      (singleFunctor (ModuleCat.{u} B) (0 : ℤ)).map (ModuleCat.ofHom α)

/-- The Hom representative of an Ext⁰ class, obtained from `H^0` of `homKaehlerDerived`
transported along `homologyZeroIso`. -/
def homOfExtZero
    (e : Ext⁽(0 : ℤ)⁾(derived A B, coeffSingle B N)) :
    Ω[B⁄A] →ₗ[B] N :=
  ((homologyZeroIso A B).inv ≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) (0 : ℤ)).inv.app
      (Algebra.cotangentComplex A B) ≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} B) (0 : ℤ)).map
      ((ShiftedHom.homEquiv (0 : ℤ) rfl).symm e) ≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) (0 : ℤ)).hom.app
      ((CochainComplex.singleFunctor (ModuleCat.{u} B) (0 : ℤ)).obj (ModuleCat.of B N)) ≫
    (singleObjHomologySelfIso (ComplexShape.up ℤ) (0 : ℤ) (ModuleCat.of B N)).hom).hom

/-- The Ext⁰ identification `Hom_B(Ω[B⁄A], N) ≃ Ext⁽0⁾(L_{B/A}, N)`. -/
def extZeroHomEquiv :
    (Ω[B⁄A] →ₗ[B] N) ≃ Ext⁽(0 : ℤ)⁾(derived A B, coeffSingle B N) where
  toFun α := ShiftedHom.homEquiv (0 : ℤ) rfl (homKaehlerDerived A B N α)
  invFun e := homOfExtZero A B N e
  left_inv := sorry
  right_inv := sorry

/-- The forward map of `extZeroHomEquiv` is `ShiftedHom.homEquiv` of `homKaehlerDerived`. -/
theorem extZeroHomEquiv_apply (α : Ω[B⁄A] →ₗ[B] N) :
    extZeroHomEquiv A B N α =
      ShiftedHom.homEquiv (0 : ℤ) rfl (homKaehlerDerived A B N α) :=
  sorry

variable {A' A B N : Type u} [CommRing A'] [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
variable {π : A' →+* A} [π.IsSquareZeroExtension]
variable {c : KernelModule π →ₗ[A] N}

/-- The identity automorphism of a solution, as a fitting map of the identity diagram. -/
def idFitting (S : Solution (B := B) (N := N) π c) :
    FittingMap (compare S S) :=
  -- Local instance justification (proof-local temporary data): bundled `S.commRing` is not globally registered on the structure Solution.
  letI := S.commRing
  -- Local instance justification (proof-local temporary data): bundled `S.isSquareZero` is not globally registered on the structure Solution.
  letI := S.isSquareZero
  FittingMap.of (compare S S) (RingHom.id S.carrier) sorry sorry sorry

/-- The underlying homomorphism of `idFitting` is the identity on the middle ring. -/
theorem idFitting_hom (S : Solution (B := B) (N := N) π c) :
    -- Local instance justification (proof-local temporary data): bundled `S.commRing` is not globally registered on the structure Solution.
    letI := S.commRing
    (idFitting S).hom = RingHom.id S.carrier :=
  sorry

end SquareZeroExtension

end RingHom

