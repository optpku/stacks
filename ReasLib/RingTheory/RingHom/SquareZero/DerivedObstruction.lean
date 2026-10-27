/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CotangentComplex.NaiveComparison.Self
public import ReasLib.RingTheory.CotangentComplex.DerivedExt
public import ReasLib.RingTheory.CotangentComplex.Transitivity
public import ReasLib.RingTheory.RingHom.SquareZero.Diagram
public import ReasLib.RingTheory.RingHom.SquareZero.IsoClass
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.BaseChange.Obstruction
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Restrict

/-!
# Derived obstructions for square-zero deformations

A square-zero surjection, an algebra over its quotient and a map on kernels
determine a canonical second-extension class of the cotangent complex.
Its vanishing characterizes solutions; first extensions act on their
isomorphism classes, and zeroth extensions classify compatible automorphisms.
The constructions use module-valued cotangent complexes of commutative rings.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory DerivedCategory HomologicalComplex ComplexShape CochainComplex
open CategoryTheory.Limits
open Algebra Algebra.Generators Algebra.Extension
open Algebra.CotangentComplex
open CommRingCat.Under.CotangentComplex
open scoped DerivedExt DerivedTensorWithAlgebra NaiveCotangent

namespace RingHom.SquareZeroExtension

variable {A' A : Type u} [CommRing A'] [CommRing A]
variable (π : A' →+* A) [π.IsSquareZeroExtension]
variable (B : Type u) [CommRing B] [Algebra A B]
variable {N : Type u} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]

/-- Derived representative transport respects the naive cotangent quotient relation. -/
private theorem toDerivedClass_well_defined :
  -- Local instance justification (noncanonical choice): the algebra structure is selected by the explicit square-zero map π.
  letI := algebraOfSquareZero π
  ∀ f g, (LinearMap.range (LinearMap.lcomp A N
        (Generators.self A' A).toExtension.cotangentComplex)).quotientRel f g →
    toDerived π B f = toDerived π B g := sorry

-- The public representative formulas unfold this private construction.
set_option backward.privateInPublic true in
/-- The derived Ext¹ class of a Hom representative of `extOneNaiveCotangent A' A N`,
aligned with restriction of scalars of `N[0]` along `A → B`. -/
private def toDerivedClass
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
  Quotient.liftOn ξ (fun f ↦ toDerived π B f) (toDerivedClass_well_defined π B)

/-- `toDerivedClass` on a Hom representative is `toDerived`. -/
private theorem toDerivedClass_mk
    (f :
      -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
      letI := algebraOfSquareZero π
      (Generators.self A' A).toExtension.Cotangent →ₗ[A] N) :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    toDerivedClass π B (extOneNaiveCotangent_mk A' A N f) = toDerived π B f :=
  rfl

-- Public computations and specifications use the private representative construction in this file.
set_option backward.privateInPublic true in
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

-- Public computations and specifications use the private representative construction in this file.
set_option backward.privateInPublic true in
/-- `xiPrimeNaive` is `extOne_adjunction` of `toDerivedClass` of the image of
`selfExtensionClass π` along `c`. -/
theorem xiPrimeNaive_eq (c : KernelModule π →ₗ[A] N) :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    xiPrimeNaive π B c =
      extOne_adjunction π B
        (toDerivedClass π B (extOneNaiveCotangent_map c (selfExtensionClass π))) :=
  rfl

/-- The Ext¹ class of the cochain-level scalar extension of `NL{A⁄A'}`, obtained by
termwise `extendScalars` of a Hom representative. -/
private def toCochainExt
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
          (selfNaiveComplex (CommRingCat.of A') (Under.mk (CommRingCat.ofHom (algebraMap A' A))))),
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
        ((ModuleCat.extendScalars (algebraMap A B)).map (ModuleCat.RestrictScalars.identityIso (R := A) (S := B) N).inv ≫
          (ModuleCat.extendRestrictScalarsAdj (algebraMap A B)).counit.app
            (ModuleCat.of B N))) ≫
    ((DerivedCategory.singleFunctors (ModuleCat.{u} B)).shiftIso (1 : ℤ) (-1) 0
        (add_neg_cancel (1 : ℤ))).inv.app (ModuleCat.of B N)

/-- `toCochainExt` on a Hom representative of the pushed tautological class. -/
private theorem toCochainExt_eq
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
            ((ModuleCat.extendScalars (algebraMap A B)).map (ModuleCat.RestrictScalars.identityIso (R := A) (S := B) N).inv ≫
              (ModuleCat.extendRestrictScalarsAdj (algebraMap A B)).counit.app
                (ModuleCat.of B N))) ≫
        ((DerivedCategory.singleFunctors (ModuleCat.{u} B)).shiftIso (1 : ℤ) (-1) 0
            (add_neg_cancel (1 : ℤ))).inv.app (ModuleCat.of B N) :=
  rfl

/-- Scalar extension of representatives respects the naive cotangent quotient relation. -/
private theorem toCochainClass_well_defined :
  -- Local instance justification (noncanonical choice): the algebra structure is selected by the explicit square-zero map π.
  letI := algebraOfSquareZero π
  -- Local instance justification (noncanonical choice): the composite algebra structure is selected by π and A → B.
  letI := algebraCompOfSquareZero π B
  -- Local instance justification (defeq pin): these algebra maps form the composite tower selected by π.
  letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
  ∀ f g, (LinearMap.range (LinearMap.lcomp A N
        (Generators.self A' A).toExtension.cotangentComplex)).quotientRel f g →
    toCochainExt π B f = toCochainExt π B g := sorry

/-- The Ext¹ class of the cochain-level scalar extension of `NL{A⁄A'}`, lifted from an
`extOneNaiveCotangent` class. -/
private def toCochainClass
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
          (selfNaiveComplex (CommRingCat.of A') (Under.mk (CommRingCat.ofHom (algebraMap A' A))))),
        coeffSingle B N) :=
  -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
  letI := algebraOfSquareZero π
  -- Local instance justification (noncanonical choice): Algebra A' B is determined by the composite of π with algebraMap A B.
  letI := algebraCompOfSquareZero π B
  -- Local instance justification (defeq pin): the tower A' → A → B is the composite of the algebra maps of π.
  letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
  Quotient.liftOn ξ (fun f ↦ toCochainExt π B f) (toCochainClass_well_defined π B)

/-- `toCochainClass` on a Hom representative is `toCochainExt`. -/
private theorem toCochainClass_mk
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
  rfl

-- The public representative formulas unfold this private construction.
set_option backward.privateInPublic true in
/-- The cochain-level scalar extension of `NL{A⁄A'}` of the pushed tautological class. -/
private def xiPrimeCochain (c : KernelModule π →ₗ[A] N) :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    -- Local instance justification (noncanonical choice): Algebra A' B is determined by the composite of π with algebraMap A B.
    letI := algebraCompOfSquareZero π B
    -- Local instance justification (defeq pin): the tower A' → A → B is the composite of the algebra maps of π.
    letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
    Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj
        (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)).obj
          (selfNaiveComplex (CommRingCat.of A') (Under.mk (CommRingCat.ofHom (algebraMap A' A))))),
        coeffSingle B N) :=
  -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
  letI := algebraOfSquareZero π
  -- Local instance justification (noncanonical choice): Algebra A' B is determined by the composite of π with algebraMap A B.
  letI := algebraCompOfSquareZero π B
  -- Local instance justification (defeq pin): the tower A' → A → B is the composite of the algebra maps of π.
  letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
  toCochainClass π B (extOneNaiveCotangent_map c (selfExtensionClass π))

/-- `xiPrimeCochain` is `toCochainClass` of the image of `selfExtensionClass π` along `c`. -/
private theorem xiPrimeCochain_eq (c : KernelModule π →ₗ[A] N) :
    -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
    letI := algebraOfSquareZero π
    -- Local instance justification (noncanonical choice): Algebra A' B is determined by the composite of π with algebraMap A B.
    letI := algebraCompOfSquareZero π B
    -- Local instance justification (defeq pin): the tower A' → A → B is the composite of the algebra maps of π.
    letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
    xiPrimeCochain π B c =
      toCochainClass π B (extOneNaiveCotangent_map c (selfExtensionClass π)) :=
  rfl

-- Public computations and specifications use the private representative construction in this file.
set_option backward.privateInPublic true in
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

/-- The second-extension obstruction assembled from `connectingMap` and `xiPrime`.
This unparameterized form uses the cone quasi-isomorphism certificate underlying
`connectingMap`; `existenceObstructionOf` takes that certificate explicitly. -/
def existenceObstruction (c : KernelModule π →ₗ[A] N) :
    Ext⁽(2 : ℤ)⁾(derived A B, coeffSingle B N) :=
  -- Local instance justification (noncanonical choice): Algebra A' A is determined by the explicit square-zero π; a global instance cannot infer π among competing ring homs.
  letI := algebraOfSquareZero π
  -- Local instance justification (noncanonical choice): Algebra A' B is determined by the composite of π with algebraMap A B.
  letI := algebraCompOfSquareZero π B
  -- Local instance justification (defeq pin): the tower A' → A → B is the composite of the algebra maps of π.
  letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
  ShiftedHom.comp (connectingMap A' A B) (xiPrime π B c) rfl

/-- The obstruction class formed using an explicit quasi-isomorphism certificate for the
cotangent mapping-cone comparison. Its localized inverse is determined by this
certificate, independently of the certificate used by `connectingMap`. -/
def existenceObstructionOf
    (hq :
      -- Local instance justification (noncanonical choice): Algebra A' A is selected by the explicit square-zero map π.
      letI := algebraOfSquareZero π
      -- Local instance justification (noncanonical choice): Algebra A' B is selected by the composite of π with algebraMap A B.
      letI := algebraCompOfSquareZero π B
      -- Local instance justification (defeq pin): the chosen composite algebra maps identify the tower A' → A → B definitionally.
      letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
      QuasiIso (fromMappingConeCochain A' A B))
    (c : KernelModule π →ₗ[A] N) :
    Ext⁽(2 : ℤ)⁾(derived A B, coeffSingle B N) :=
  -- Local instance justification (noncanonical choice): Algebra A' A is selected by the explicit square-zero map π.
  letI := algebraOfSquareZero π
  -- Local instance justification (noncanonical choice): Algebra A' B is selected by the composite of π with algebraMap A B.
  letI := algebraCompOfSquareZero π B
  -- Local instance justification (defeq pin): the chosen composite algebra maps identify the tower A' → A → B definitionally.
  letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
  ShiftedHom.comp
    ((Localization.isoOfHom DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat B) (ComplexShape.up ℤ))
      (fromMappingConeCochain A' A B) hq).inv ≫
      DerivedCategory.Q.map (mappingCone.triangle (tensorMapCochain A' A B)).mor₃ ≫
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (tensorCochain A' A B))
    (xiPrime π B c) rfl

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
  rfl


section Identity

variable {A' A B N : Type u} [CommRing A'] [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
variable {π : A' →+* A} [π.IsSquareZeroExtension]
variable {c : KernelModule π →ₗ[A] N}

/-- The identity ring homomorphism commutes with the projection of a solution. -/
theorem idFitting_comm_toB (S : Solution (B := B) (N := N) π c) :
  -- Local instance justification (proof-local temporary data): the ring structure on the carrier is stored in S.
  letI := S.commRing
  S.toB.comp (RingHom.id S.carrier) = (compare S S).g.comp S.toB := sorry

/-- The identity ring homomorphism commutes with the structure map of a solution. -/
theorem idFitting_comm_fromA (S : Solution (B := B) (N := N) π c) :
  -- Local instance justification (proof-local temporary data): the ring structure on the carrier is stored in S.
  letI := S.commRing
  (RingHom.id S.carrier).comp S.fromA' = S.fromA'.comp (compare S S).t' := sorry

/-- The identity ring homomorphism induces the identity map on the identified square-zero kernel. -/
theorem idFitting_induces (S : Solution (B := B) (N := N) π c) :
  -- Local instance justification (proof-local temporary data): the ring structure on the carrier is stored in S.
  letI := S.commRing
  -- Local instance justification (proof-local temporary data): the square-zero structure on the projection is stored in S.
  letI := S.isSquareZero
  ∀ x : KernelModule S.toB,
    S.kernelEquiv (kerMapOfHoms (RingHom.id S.carrier) (compare S S).g
      (idFitting_comm_toB S) x) = (compare S S).ν (S.kernelEquiv x) := sorry

/-- The identity automorphism of a solution, as a fitting map of the identity diagram. -/
def idFitting (S : Solution (B := B) (N := N) π c) :
    FittingMap (compare S S) :=
  -- Local instance justification (proof-local temporary data): bundled `S.commRing` is not globally registered on the structure Solution.
  letI := S.commRing
  -- Local instance justification (proof-local temporary data): bundled `S.isSquareZero` is not globally registered on the structure Solution.
  letI := S.isSquareZero
  FittingMap.of (compare S S) (RingHom.id S.carrier)
    (idFitting_comm_toB S) (idFitting_comm_fromA S) (idFitting_induces S)

/-- The underlying homomorphism of `idFitting` is the identity on the middle ring. -/
theorem idFitting_hom (S : Solution (B := B) (N := N) π c) :
    -- Local instance justification (proof-local temporary data): bundled `S.commRing` is not globally registered on the structure Solution.
    letI := S.commRing
    (idFitting S).hom = RingHom.id S.carrier :=
  rfl


end Identity

variable (c : KernelModule π →ₗ[A] N)

/-- The canonical second-extension obstruction vanishes exactly when a compatible square-zero solution exists. -/
theorem existenceObstruction_eq_zero_iff :
    existenceObstruction π B c = 0 ↔ Nonempty (Solution (B := B) (N := N) π c) :=
  sorry

/-- With an explicit cone-comparison certificate, vanishing of the obstruction is
equivalent to existence of a compatible square-zero solution. -/
theorem existenceObstructionOf_eq_zero_iff
    (hq :
      -- Local instance justification (noncanonical choice): Algebra A' A is selected by the explicit square-zero map π.
      letI := algebraOfSquareZero π
      -- Local instance justification (noncanonical choice): Algebra A' B is selected by the composite of π with algebraMap A B.
      letI := algebraCompOfSquareZero π B
      -- Local instance justification (defeq pin): the chosen composite algebra maps identify the tower A' → A → B definitionally.
      letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
      QuasiIso (fromMappingConeCochain A' A B)) :
    existenceObstructionOf π B hq c = 0 ↔
      Nonempty (Solution (B := B) (N := N) π c) := sorry

/-- Full-cotangent first extensions translate solution classes using the inverse of
the canonical naive-to-derived comparison certified by explicit bijectivity. -/
def derivedVaddOf (hbij : Function.Bijective (extOneNaiveDerivedHom A B N))
    (ξ : Ext⁽(1 : ℤ)⁾(derived A B, coeffSingle B N)) (p : IsoClass π B c) : IsoClass π B c :=
  vadd ((extOneNaiveDerivedEquivOf A B N hbij).symm ξ) p

/-- The difference of two solution classes, transported to full-cotangent Ext¹
using explicitly certified bijectivity of the canonical comparison. -/
def derivedVsubOf (hbij : Function.Bijective (extOneNaiveDerivedHom A B N))
    (p q : IsoClass π B c) : Ext⁽(1 : ℤ)⁾(derived A B, coeffSingle B N) :=
  extOneNaiveDerivedEquivOf A B N hbij (vsub p q)

/-- Full-cotangent first extensions translate isomorphism classes of square-zero solutions,
using `extOneNaiveDerivedHom_bijective` as the comparison certificate. -/
def derivedVadd (ξ : Ext⁽(1 : ℤ)⁾(derived A B, coeffSingle B N)) (p : IsoClass π B c) : IsoClass π B c :=
  derivedVaddOf π B c (extOneNaiveDerivedHom_bijective A B N) ξ p

/-- The difference of two solution classes as a full-cotangent first extension,
using `extOneNaiveDerivedHom_bijective` as the comparison certificate. -/
def derivedVsub (p q : IsoClass π B c) : Ext⁽(1 : ℤ)⁾(derived A B, coeffSingle B N) :=
  derivedVsubOf π B c (extOneNaiveDerivedHom_bijective A B N) p q

/-- Translation by the zero first-extension class fixes every solution class. -/
theorem derivedVadd_zero (p : IsoClass π B c) :
    derivedVadd π B c 0 p = p := sorry

/-- Translation by a sum of first extensions is the composite of their translations. -/
theorem derivedVadd_add (ξ η : Ext⁽(1 : ℤ)⁾(derived A B, coeffSingle B N)) (p : IsoClass π B c) :
    derivedVadd π B c (ξ + η) p =
      derivedVadd π B c ξ (derivedVadd π B c η p) := sorry

/-- Translating a solution class by its difference from another class recovers it. -/
theorem derivedVsub_vadd (p q : IsoClass π B c) :
    derivedVadd π B c (derivedVsub π B c p q) q = p := sorry

/-- The difference of a translated solution class from the original is the translation class. -/
theorem derivedVadd_vsub (ξ : Ext⁽(1 : ℤ)⁾(derived A B, coeffSingle B N)) (p : IsoClass π B c) :
    derivedVsub π B c (derivedVadd π B c ξ p) p = ξ := sorry

/-- A solution makes its isomorphism classes an additive torsor under full-cotangent
Ext¹, with translation defined using explicit bijectivity of the canonical comparison. -/
@[reducible]
def derivedAddTorsorOf (hbij : Function.Bijective (extOneNaiveDerivedHom A B N))
    (S0 : Solution (B := B) (N := N) π c) :
    AddTorsor (Ext⁽(1 : ℤ)⁾(derived A B, coeffSingle B N)) (IsoClass π B c) where
  vadd := derivedVaddOf π B c hbij
  zero_vadd := derivedVadd_zero π B c
  add_vadd := derivedVadd_add π B c
  vsub := derivedVsubOf π B c hbij
  nonempty := ⟨isoClassMk S0⟩
  vsub_vadd' := derivedVsub_vadd π B c
  vadd_vsub' := derivedVadd_vsub π B c

/-- A solution makes its isomorphism classes an additive torsor under full-cotangent Ext¹,
using `extOneNaiveDerivedHom_bijective` as the comparison certificate. -/
@[reducible]
def derivedAddTorsor (S0 : Solution (B := B) (N := N) π c) :
    AddTorsor (Ext⁽(1 : ℤ)⁾(derived A B, coeffSingle B N)) (IsoClass π B c) :=
  derivedAddTorsorOf π B c (extOneNaiveDerivedHom_bijective A B N) S0

/-- A chosen solution identifies solution classes with full-cotangent first extensions,
using an explicit bijectivity certificate for the canonical comparison. -/
def isoClassDerivedEquivOf (hbij : Function.Bijective (extOneNaiveDerivedHom A B N))
    (S0 : Solution (B := B) (N := N) π c) :
    Ext⁽(1 : ℤ)⁾(derived A B, coeffSingle B N) ≃ IsoClass π B c :=
  (extOneNaiveDerivedEquivOf A B N hbij).toEquiv.symm.trans (isoClassEquiv S0)

/-- A chosen solution identifies solution classes with full-cotangent first extensions,
using `extOneNaiveDerivedHom_bijective` as the comparison certificate. -/
def isoClassDerivedEquiv (S0 : Solution (B := B) (N := N) π c) :
    Ext⁽(1 : ℤ)⁾(derived A B, coeffSingle B N) ≃ IsoClass π B c :=
  isoClassDerivedEquivOf π B c (extOneNaiveDerivedHom_bijective A B N) S0

/-- The based chart sends a derived Ext¹ class to the translate of the basepoint. -/
theorem isoClassDerivedEquiv_apply (S0 : Solution (B := B) (N := N) π c)
    (ξ : Ext⁽(1 : ℤ)⁾(derived A B, coeffSingle B N)) :
    isoClassDerivedEquiv π B c S0 ξ =
      isoClassEquiv S0 ((extOneNaiveDerivedEquiv A B N).symm ξ) :=
  rfl

/-- The zero Ext¹ class is sent to the class of the basepoint. -/
theorem isoClassDerivedEquiv_zero (S0 : Solution (B := B) (N := N) π c) :
    isoClassDerivedEquiv π B c S0 0 = isoClassMk S0 :=
  sorry

/-- The inverse chart is the naive torsor subtraction, transported along
`extOneNaiveDerivedEquiv`. -/
theorem isoClassDerivedEquiv_symm_apply (S0 : Solution (B := B) (N := N) π c)
    (p : IsoClass π B c) :
    (isoClassDerivedEquiv π B c S0).symm p =
      extOneNaiveDerivedEquiv A B N ((isoClassEquiv S0).symm p) :=
  rfl

/-- Perturbing the identity by a differential and taking its difference recovers the Ext⁰ class. -/
theorem autEquiv_left_inv (S : Solution (B := B) (N := N) π c)
    (e : Ext⁽(0 : ℤ)⁾(derived A B, coeffSingle B N)) :
  -- Local instance justification (noncanonical choice): the coefficient action is restriction along the identity map in compare S S.
  letI := RelativeDiagram.moduleRestrict (compare S S)
  extZeroHomEquiv A B N
    (FittingMap.diff (compare S S) (idFitting S)
      (FittingMap.perturb (compare S S) ((extZeroHomEquiv A B N).symm e)
        (idFitting S))) = e := sorry

/-- Perturbing the identity by the difference of a fitting automorphism recovers that automorphism. -/
theorem autEquiv_right_inv (S : Solution (B := B) (N := N) π c) (φ : FittingMap (compare S S)) :
  -- Local instance justification (noncanonical choice): the coefficient action is restriction along the identity map in compare S S.
  letI := RelativeDiagram.moduleRestrict (compare S S)
  FittingMap.perturb (compare S S)
    ((extZeroHomEquiv A B N).symm
      (extZeroHomEquiv A B N (FittingMap.diff (compare S S) (idFitting S) φ)))
    (idFitting S) = φ := sorry

/-- Compatible automorphisms of a solution are canonically its full-cotangent zeroth extensions. -/
def autEquiv (S : Solution (B := B) (N := N) π c) :
    Ext⁽(0 : ℤ)⁾(derived A B, coeffSingle B N) ≃ FittingMap (compare S S) where
  toFun e :=
    -- Local instance justification (noncanonical choice): the B-action on N along compare S S is restriction along id.
    letI := RelativeDiagram.moduleRestrict (compare S S)
    FittingMap.perturb (compare S S) ((extZeroHomEquiv A B N).symm e) (idFitting S)
  invFun φ :=
    -- Local instance justification (noncanonical choice): the B-action on N along compare S S is restriction along id.
    letI := RelativeDiagram.moduleRestrict (compare S S)
    extZeroHomEquiv A B N (FittingMap.diff (compare S S) (idFitting S) φ)
  left_inv := autEquiv_left_inv π B c S
  right_inv := autEquiv_right_inv π B c S

/-- The forward map of `autEquiv` sends an Ext⁰ class to the perturbation of `idFitting`. -/
theorem autEquiv_apply (S : Solution (B := B) (N := N) π c)
    (e : Ext⁽(0 : ℤ)⁾(derived A B, coeffSingle B N)) :
    autEquiv π B c S e =
      FittingMap.perturb (compare S S) ((extZeroHomEquiv A B N).symm e) (idFitting S) :=
  rfl


end SquareZeroExtension

end RingHom
