/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Extension.Cotangent.Obstruction
public import Mathlib.Algebra.Homology.Single
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Ext.Functor
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.BaseChange
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Canonical
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Derived
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.ExtendScalars
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.SquareZeroComparison

/-! # Derived comparisons for presentation obstruction modules -/

@[expose] public section

set_option backward.privateInPublic true
open CategoryTheory Algebra Algebra.Generators Algebra.Extension MvPolynomial
open scoped NaiveCotangent
noncomputable section
universe u
namespace Algebra.NaiveCotangent.Obstruction

/-- The degree-one map of the presentation complex associated to a relation homomorphism. -/
private def presentationDegreeOne {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (f : relationHom J φ (RingHom.SquareZeroExtension.KernelModule π.toRingHom)) :
    (NaiveCotangent.complex (Generators.naive (I := J)).toExtension).X 1 ⟶
      ((ModuleCat.restrictScalars φ.toRingHom).obj
      (ModuleCat.of A (RingHom.SquareZeroExtension.KernelModule π.toRingHom))) :=
  ConcreteCategory.ofHom
    ({ toFun := fun y ↦ f (NaiveCotangent.liftEquiv (Generators.naive (I := J)).toExtension y)
       map_add' := sorry
       map_smul' := sorry } :
      NaiveCotangent.Lift (Generators.naive (I := J)).toExtension →ₗ[MvPolynomial ι Λ ⧸ J]
        (ModuleCat.restrictScalars φ.toRingHom).obj
          (ModuleCat.of A (RingHom.SquareZeroExtension.KernelModule π.toRingHom)))

/-- Differentials into degree one vanish after the presentation degree-one map. -/
private theorem presentationToSingle_d_comp {Λ ι A' A : Type u}
    [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (f : (NaiveCotangent.complex (Generators.naive (I := J)).toExtension).X 1 ⟶
      ((ModuleCat.restrictScalars φ.toRingHom).obj
      (ModuleCat.of A (RingHom.SquareZeroExtension.KernelModule π.toRingHom))))
    (i : ℕ) (hi : (ComplexShape.down ℕ).Rel i 1) :
    (NaiveCotangent.complex (Generators.naive (I := J)).toExtension).d i 1 ≫ f = 0 :=
  sorry

/-- Chain map from the presentation complex to `I[1]`, zero in degree 0. -/
private def presentationToSingle {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (f : relationHom J φ (RingHom.SquareZeroExtension.KernelModule π.toRingHom)) :
    NaiveCotangent.complex (Generators.naive (I := J)).toExtension ⟶
      (HomologicalComplex.single
        (ModuleCat (MvPolynomial ι Λ ⧸ J)) (ComplexShape.down ℕ) 1).obj
        (((ModuleCat.restrictScalars φ.toRingHom).obj
      (ModuleCat.of A (RingHom.SquareZeroExtension.KernelModule π.toRingHom)))) :=
  HomologicalComplex.mkHomToSingle (presentationDegreeOne π J φ f)
    (presentationToSingle_d_comp π J φ (presentationDegreeOne π J φ f))

/-- Derived morphism associated to a chain map into a degree-one single complex. -/
private def derivedFromSingle {R : Type u} [CommRing R]
    {K : ChainComplex (ModuleCat R) ℕ} {N : ModuleCat R}
    (toSingle : K ⟶
      (HomologicalComplex.single (ModuleCat R) (ComplexShape.down ℕ) 1).obj N) :
    DerivedCategory.Q.obj (K.extend ComplexShape.embeddingDownNat) ⟶
      ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj N)⟦(1 : ℤ)⟧ :=
  DerivedCategory.Q.map (HomologicalComplex.extendMap toSingle
      ComplexShape.embeddingDownNat) ≫
    DerivedCategory.Q.map
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
        N 1 (-1 : ℤ) rfl).hom ≫
    ((DerivedCategory.singleFunctors (ModuleCat R)).shiftIso (1 : ℤ) (-1) 0
      (add_neg_cancel (1 : ℤ))).inv.app N

/-- Linear comparison from the Hom-coker to `Ext¹_R(NL{R⁄Λ}, I)`. -/
def extMap {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    ((ModuleCat.restrictScalars φ.toRingHom).obj
        (ModuleCat.of A (module π J φ))) →ₗ[MvPolynomial ι Λ ⧸ J]
      (DerivedCategory.Ext.moduleFunctor
      (Algebra.naiveCotangentObject Λ (MvPolynomial ι Λ ⧸ J)) (1 : ℤ)).obj (((ModuleCat.restrictScalars φ.toRingHom).obj
      (ModuleCat.of A (RingHom.SquareZeroExtension.KernelModule π.toRingHom)))) where
  toFun x := QuotientAddGroup.lift _
    { toFun := fun f ↦ derivedFromSingle
        ((NaiveCotangent.generatorsHomotopyEquiv
      (Generators.self Λ (MvPolynomial ι Λ ⧸ J)) (Generators.naive (I := J))).hom ≫ presentationToSingle π J φ f)
      map_zero' := sorry
      map_add' := sorry } sorry x
  map_add' := sorry
  map_smul' := sorry

/-- `extMap` sends a Hom-coker class to the derived morphism of its presentation chain map. -/
theorem extMap_apply {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (f : relationHom J φ (RingHom.SquareZeroExtension.KernelModule π.toRingHom)) :
    extMap π J φ (Submodule.Quotient.mk f) =
      derivedFromSingle
        ((NaiveCotangent.generatorsHomotopyEquiv
      (Generators.self Λ (MvPolynomial ι Λ ⧸ J)) (Generators.naive (I := J))).hom ≫ presentationToSingle π J φ f) :=
  sorry

/-- Linear comparison from the Hom-coker to `Ext¹_R(NL{R⁄Λ}, I)`. -/
theorem extMap_bijective {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    Function.Bijective (extMap π J φ) := sorry

/-- The two-term tensor model of `NL{R⁄Λ} ⊗_R A` along `φ`. -/
def tensorModel {Λ ι A : Type u} [CommRing Λ] [CommRing A] [Algebra Λ A]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    ChainComplex (ModuleCat A) ℕ :=
  -- Local instance justification (noncanonical choice): the R-algebra structure on A is induced by explicit φ; competing algebra maps prevent a global inferred choice.
  letI : Algebra (MvPolynomial ι Λ ⧸ J) A := φ.toRingHom.toAlgebra
  -- Local instance justification (noncanonical choice): the tower Λ → R → A is induced by φ.
  letI : IsScalarTower Λ (MvPolynomial ι Λ ⧸ J) A :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  NaiveCotangent.BaseChange.tensorModel (Generators.naive (I := J)).toExtension

/-- The degree-one map of the tensor model associated to a relation homomorphism. -/
private def tensorDegreeOne {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (f : relationHom J φ (RingHom.SquareZeroExtension.KernelModule π.toRingHom)) :
    (tensorModel J φ).X 1 ⟶ ModuleCat.of A (RingHom.SquareZeroExtension.KernelModule π.toRingHom) :=
  -- Local instance justification (noncanonical choice): the R-algebra structure on A is induced by explicit φ; competing algebra maps prevent a global inferred choice.
  letI : Algebra (MvPolynomial ι Λ ⧸ J) A := φ.toRingHom.toAlgebra
  -- Local instance justification (noncanonical choice): the tower Λ → R → A is induced by φ.
  letI : IsScalarTower Λ (MvPolynomial ι Λ ⧸ J) A :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  -- Local instance justification (noncanonical choice): I is an R-module along φ.
  letI : Module (MvPolynomial ι Λ ⧸ J) (RingHom.SquareZeroExtension.KernelModule π.toRingHom) :=
    Module.compHom (RingHom.SquareZeroExtension.KernelModule π.toRingHom) φ.toRingHom
  -- Local instance justification (noncanonical choice): the R-action on I via φ is compatible with the A-action.
  letI : IsScalarTower (MvPolynomial ι Λ ⧸ J) A (RingHom.SquareZeroExtension.KernelModule π.toRingHom) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  ModuleCat.ofHom
    (LinearMap.liftBaseChange A
      { toFun := f.toFun
        map_add' := sorry
        map_smul' := sorry })

/-- Differentials into degree one vanish after the tensor-model degree-one map. -/
private theorem tensorToSingle_d_comp {Λ ι A' A : Type u}
    [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (f : (tensorModel J φ).X 1 ⟶ ModuleCat.of A (RingHom.SquareZeroExtension.KernelModule π.toRingHom))
    (i : ℕ) (hi : (ComplexShape.down ℕ).Rel i 1) :
    (tensorModel J φ).d i 1 ≫ f = 0 :=
  sorry

/-- Chain map from the tensor model to `I[1]`, zero in degree 0. -/
private def tensorToSingle {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (f : relationHom J φ (RingHom.SquareZeroExtension.KernelModule π.toRingHom)) :
    tensorModel J φ ⟶
      (HomologicalComplex.single (ModuleCat A) (ComplexShape.down ℕ) 1).obj
        (ModuleCat.of A (RingHom.SquareZeroExtension.KernelModule π.toRingHom)) :=
  HomologicalComplex.mkHomToSingle (tensorDegreeOne π J φ f)
    (tensorToSingle_d_comp π J φ (tensorDegreeOne π J φ f))

/-- Linear comparison from the Hom-coker to `Ext¹_A(NL{R⁄Λ} ⊗_R A, I)`. -/
def baseChangeExtMap {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    module π J φ →ₗ[A]
      (DerivedCategory.Ext.moduleFunctor
        (DerivedCategory.Q.obj ((tensorModel J φ).extend ComplexShape.embeddingDownNat))
        (1 : ℤ)).obj (ModuleCat.of A (RingHom.SquareZeroExtension.KernelModule π.toRingHom)) where
  toFun x := QuotientAddGroup.lift _
    { toFun := fun f ↦ derivedFromSingle (tensorToSingle π J φ f)
      map_zero' := sorry
      map_add' := sorry } sorry x
  map_add' := sorry
  map_smul' := sorry

/-- `baseChangeExtMap` sends a Hom-coker class to the derived morphism of its tensor chain map. -/
theorem baseChangeExtMap_apply {Λ ι A' A : Type u}
    [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (f : relationHom J φ (RingHom.SquareZeroExtension.KernelModule π.toRingHom)) :
    baseChangeExtMap π J φ (Submodule.Quotient.mk f) =
      derivedFromSingle (tensorToSingle π J φ f) :=
  sorry

/-- Linear comparison from the Hom-coker to `Ext¹_A(NL{R⁄Λ} ⊗_R A, I)`. -/
theorem baseChangeExtMap_bijective {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    Function.Bijective (baseChangeExtMap π J φ) := sorry

/-- The obstruction module identifies with the free-coordinate Hom cokernel and both derived Ext modules. -/
theorem module_spec {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    Function.Bijective (homCokerMap π J φ) ∧
      Function.Bijective (extMap π J φ) ∧
      Function.Bijective (baseChangeExtMap π J φ) :=
  ⟨homCokerMap_bijective π J φ, extMap_bijective π J φ, baseChangeExtMap_bijective π J φ⟩

/-- The structure map of `π.toRingHom.toAlgebra` is surjective. -/
private theorem squareZero_algebraMap_surjective {Λ A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A] (π : A' →ₐ[Λ] A)
    [π.toRingHom.IsSquareZeroExtension] :
    Function.Surjective (@algebraMap A' A _ _ (π.toRingHom.toAlgebra)) :=
  (inferInstance : π.toRingHom.IsSquareZeroExtension).surjective

/-- The empty-generator presentation of a square-zero surjection. -/
private def squareZeroPresentation {Λ A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A] (π : A' →ₐ[Λ] A)
    [π.toRingHom.IsSquareZeroExtension] :
    @Generators A' A PEmpty.{u + 1} _ _ (π.toRingHom.toAlgebra) :=
  @Generators.ofSurjectiveAlgebraMap A' A _ _ (π.toRingHom.toAlgebra)
    (squareZero_algebraMap_surjective π)

/-- The two-term naive cotangent complex of the empty presentation of `π`. -/
private abbrev squareZeroComplex {Λ A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A] (π : A' →ₐ[Λ] A)
    [π.toRingHom.IsSquareZeroExtension] :
    ChainComplex (ModuleCat A) ℕ :=
  -- Local instance justification (noncanonical choice): the A'-algebra structure on A is induced by explicit π; competing algebra maps prevent a global inferred choice.
  letI : Algebra A' A := π.toRingHom.toAlgebra
  Extension.NaiveCotangent.complex (squareZeroPresentation π).toExtension

/-- The lifted conormal module of the empty presentation of `π`. -/
private abbrev squareZeroLift {Λ A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A] (π : A' →ₐ[Λ] A)
    [π.toRingHom.IsSquareZeroExtension] : Type u :=
  -- Local instance justification (noncanonical choice): the A'-algebra structure on A is induced by explicit π; competing algebra maps prevent a global inferred choice.
  letI : Algebra A' A := π.toRingHom.toAlgebra
  Extension.NaiveCotangent.Lift (squareZeroPresentation π).toExtension

/-- The cotangent space of a square-zero empty presentation is a subsingleton. -/
private theorem squareZero_cotangentSpace_subsingleton {Λ A' A : Type u}
    [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A] (π : A' →ₐ[Λ] A)
    [π.toRingHom.IsSquareZeroExtension] :
    -- Local instance justification (noncanonical choice): the A'-algebra structure on A is induced by explicit π; competing algebra maps prevent a global inferred choice.
    letI : Algebra A' A := π.toRingHom.toAlgebra
    Subsingleton (squareZeroPresentation π).toExtension.CotangentSpace :=
  sorry

/-- Canonical homotopy equivalence from `NL{A⁄A'}` to the empty-generator presentation complex. -/
private def homotopyEquiv_squareZero {Λ A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A] (π : A' →ₐ[Λ] A)
    [π.toRingHom.IsSquareZeroExtension] :
    HomotopyEquiv (RingHom.naiveCotangent π.toRingHom) (squareZeroComplex π) :=
  -- Local instance justification (noncanonical choice): the A'-algebra structure on A is induced by explicit π; competing algebra maps prevent a global inferred choice.
  letI : Algebra A' A := π.toRingHom.toAlgebra
  Extension.NaiveCotangent.generatorsHomotopyEquiv
    (Generators.self A' A) (squareZeroPresentation π)

/-- The differential into the degree-one projection of the empty presentation vanishes. -/
private theorem squareZeroToSingle_d_comp {Λ A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension] :
    -- Local instance justification (noncanonical choice): explicit π selects the A'-algebra structure on A.
    letI : Algebra A' A := π.toRingHom.toAlgebra
    ∀ (i : ℕ) (hi : (ComplexShape.down ℕ).Rel i 1),
      (squareZeroComplex π).d i 1 ≫
        (@Extension.NaiveCotangent.componentOneIso A' A _ _
          (π.toRingHom.toAlgebra) (squareZeroPresentation π).toExtension).hom = 0 :=
  sorry

/-- The empty-presentation complex maps to its degree-one single complex. -/
private def squareZeroToSingle {Λ A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A] (π : A' →ₐ[Λ] A)
    [π.toRingHom.IsSquareZeroExtension] :
    squareZeroComplex π ⟶
      ((HomologicalComplex.single (ModuleCat A) (ComplexShape.down ℕ) 1).obj
        (ModuleCat.of A (squareZeroLift π))) :=
  -- Local instance justification (noncanonical choice): the A'-algebra structure on A is induced by explicit π; competing algebra maps prevent a global inferred choice.
  letI : Algebra A' A := π.toRingHom.toAlgebra
  HomologicalComplex.mkHomToSingle
    (Extension.NaiveCotangent.componentOneIso
      (squareZeroPresentation π).toExtension).hom
    (squareZeroToSingle_d_comp π)

/-- Linear comparison from the lifted conormal module of `π` to the square-zero kernel. -/
private def squareZeroLiftToKernel {Λ A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A] (π : A' →ₐ[Λ] A)
    [π.toRingHom.IsSquareZeroExtension] :
    squareZeroLift π →ₗ[A] RingHom.SquareZeroExtension.KernelModule π.toRingHom :=
  -- Local instance justification (noncanonical choice): explicit π selects the A'-algebra structure on A; competing algebra maps prevent a global inferred choice.
  letI : Algebra A' A := π.toRingHom.toAlgebra
  { toFun := fun x ↦
      (RingHom.SquareZeroExtension.toCotangentEquiv π.toRingHom).symm
        (QuotientAddGroup.lift _
          { toFun := fun f : (squareZeroPresentation π).ker ↦
              Ideal.toCotangent (RingHom.ker π.toRingHom) ⟨constantCoeff f.1, sorry⟩
            map_zero' := sorry
            map_add' := sorry } sorry
          ((NaiveCotangent.liftEquiv (squareZeroPresentation π).toExtension x).val))
    map_add' := sorry
    map_smul' := sorry }

/-- Identification of the lifted conormal module of `π` with the square-zero kernel. -/
private theorem squareZeroLiftToKernel_bijective {Λ A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A] (π : A' →ₐ[Λ] A)
    [π.toRingHom.IsSquareZeroExtension] :
    Function.Bijective (squareZeroLiftToKernel π) := sorry

/-- The square-zero naive cotangent complex maps canonically to its kernel in degree one. -/
def squareZeroToKernel {Λ A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A] (π : A' →ₐ[Λ] A)
    [π.toRingHom.IsSquareZeroExtension] :
    RingHom.naiveCotangent π.toRingHom ⟶
      (HomologicalComplex.single (ModuleCat A) (ComplexShape.down ℕ) 1).obj
        (ModuleCat.of A (RingHom.SquareZeroExtension.KernelModule π.toRingHom)) :=
  (homotopyEquiv_squareZero π).hom ≫ squareZeroToSingle π ≫
    (HomologicalComplex.single (ModuleCat A) (ComplexShape.down ℕ) 1).map
      (ModuleCat.ofHom (squareZeroLiftToKernel π))

/-- The canonical map to the square-zero kernel is a quasi-isomorphism. -/
instance instQuasiIsoSquareZeroToKernel {Λ A' A : Type u}
    [CommRing Λ] [CommRing A'] [CommRing A] [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension] :
    QuasiIso (squareZeroToKernel π) := sorry

/-- Source-changing comparison `NL{A⁄Λ} ⟶ NL{A⁄A'}` along `π`. -/
private def toSquareZero {Λ A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A] (π : A' →ₐ[Λ] A) :
    NL{A ⁄ Λ} ⟶ @Algebra.naiveCotangent A' A _ _ π.toRingHom.toAlgebra :=
  -- Local instance justification (noncanonical choice): the A'-algebra structure on A is induced by explicit π; competing algebra maps prevent a global inferred choice.
  letI : Algebra A' A := π.toRingHom.toAlgebra
  -- Local instance justification (noncanonical choice): the tower Λ → A' → A is induced by π.
  letI : IsScalarTower Λ A' A := IsScalarTower.of_algebraMap_eq' π.comp_algebraMap.symm
  NaiveCotangent.chainMap
    (Generators.defaultHom (Generators.self Λ A) (Generators.self A' A)).toExtensionHom

/-- Target-changing comparison from the tensor model of `R` to `NL{A⁄Λ}`. -/
private def toTarget {Λ ι A : Type u} [CommRing Λ] [CommRing A] [Algebra Λ A]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    tensorModel J φ ⟶ Algebra.naiveCotangent Λ A :=
  -- Local instance justification (noncanonical choice): the R-algebra structure on A is induced by explicit φ; competing algebra maps prevent a global inferred choice.
  letI : Algebra (MvPolynomial ι Λ ⧸ J) A := φ.toRingHom.toAlgebra
  -- Local instance justification (noncanonical choice): the tower Λ → R → A is induced by φ.
  letI : IsScalarTower Λ (MvPolynomial ι Λ ⧸ J) A :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  (NaiveCotangent.BaseChange.scalarExtensionIsoTensorModel
      (Generators.naive (I := J)).toExtension).inv ≫
    NaiveCotangent.ExtendScalars.map
      (Generators.defaultHom (Generators.naive (I := J)) (Generators.self Λ A)).toExtensionHom

/-- The chain-level composite `NL{R⁄Λ} ⊗_R A ⟶ NL{A⁄Λ} ⟶ NL{A⁄A'} ⟶ I[1]`. -/
private def compositionChain {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    tensorModel J φ ⟶
      (HomologicalComplex.single (ModuleCat A) (ComplexShape.down ℕ) 1).obj
        (ModuleCat.of A (RingHom.SquareZeroExtension.KernelModule π.toRingHom)) :=
  toTarget J φ ≫ toSquareZero π ≫ squareZeroToKernel π

/-- The derived morphism `NL{R⁄Λ} ⊗_R A ⟶ I[1]` in `D(A)`. -/
public def composition {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    DerivedCategory.Q.obj ((tensorModel J φ).extend ComplexShape.embeddingDownNat) ⟶
      ((DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)).obj
        (ModuleCat.of A (RingHom.SquareZeroExtension.KernelModule π.toRingHom)))⟦(1 : ℤ)⟧ :=
  derivedFromSingle (compositionChain π J φ)

/-- The obstruction class equals the derived composition under the Ext identification. -/
theorem eq_composition {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    baseChangeExtMap π J φ (obstruction π J φ) = composition π J φ :=
  sorry

end Algebra.NaiveCotangent.Obstruction
