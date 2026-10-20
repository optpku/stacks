/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Adjunction
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Canonical
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Derived
public import stacks_project.Chap92.Remark_92_11_4
public import stacks_project.Chap92.«92_7_0_1_Triangle»

/-!
# Under self-presentation vs Generators.self naive cotangent comparison

The categorical self-presentation `A[B] ⟶ B` and the polynomial self-presentation
`Generators.self A B` determine isomorphic two-term naive cotangent complexes.
Degree `0` is identified by `polynomialIso` and `CommRingCat.KaehlerDifferential.map`;
degree `-1` is identified by `Ideal.toCotangent` on the two kernels.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory DerivedCategory HomologicalComplex ComplexShape
open DerivedCategory.TStructure
open Algebra Algebra.Generators Algebra.Extension
open Algebra.CotangentComplex
open Algebra.NaiveCotangent
open CommRingCat.Under.CotangentComplex
open CommRingCat.Under.FreeAlgebra
open scoped ChangeOfRings TensorProduct

namespace RingHom.SquareZeroExtension

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- Evaluation of the categorical free algebra is polynomial evaluation after `polynomialIso`. -/
theorem selfHom_comp_polynomialIso :
    (selfHom (CommRingCat.of A) (under A B)).right.hom =
      (algebraMap (Generators.self A B).Ring B).comp
        (polynomialIso (CommRingCat.of A) B).hom.right.hom :=
  sorry

/-- Polynomial evaluation is categorical evaluation after `polynomialIso.inv`. -/
theorem algebraMap_comp_polynomialIso_inv :
    (algebraMap (Generators.self A B).Ring B) =
      (selfHom (CommRingCat.of A) (under A B)).right.hom.comp
        (polynomialIso (CommRingCat.of A) B).inv.right.hom :=
  sorry

/-- `polynomialIso` sends the kernel of the categorical counit into the kernel of polynomial
evaluation. -/
theorem polynomialIso_ker_le :
    RingHom.ker (selfHom (CommRingCat.of A) (under A B)).right.hom ≤
      Ideal.comap (polynomialIso (CommRingCat.of A) B).hom.right.hom
        (RingHom.ker (algebraMap (Generators.self A B).Ring B)) :=
  sorry

/-- `polynomialIso.inv` sends the kernel of polynomial evaluation into the kernel of the
categorical counit. -/
theorem polynomialIso_inv_ker_le :
    RingHom.ker (algebraMap (Generators.self A B).Ring B) ≤
      Ideal.comap (polynomialIso (CommRingCat.of A) B).inv.right.hom
        (RingHom.ker (selfHom (CommRingCat.of A) (under A B)).right.hom) :=
  sorry

/-- The adjunction unit from polynomial Kähler differentials into the restricted
scalar extension. -/
def selfNaiveCotangentSpaceUnit :
    CommRingCat.KaehlerDifferential (polynomial (CommRingCat.of A) B).hom ⟶
      (ModuleCat.restrictScalars (algebraMap (Generators.self A B).Ring B)).obj
        ((ModuleCat.extendScalars (algebraMap (Generators.self A B).Ring B)).obj
          (CommRingCat.KaehlerDifferential (polynomial (CommRingCat.of A) B).hom)) :=
  (ModuleCat.extendRestrictScalarsAdj
      (algebraMap (Generators.self A B).Ring B)).unit.app
    (CommRingCat.KaehlerDifferential (polynomial (CommRingCat.of A) B).hom)

/-- The restricted comparison from Under self-presentation differentials to the
extended polynomial Kähler object. -/
def selfNaiveDifferentialsRestrict :
    CommRingCat.KaehlerDifferential ((functor (CommRingCat.of A)).obj B).hom ⟶
      (ModuleCat.restrictScalars
          (selfHom (CommRingCat.of A) (under A B)).right.hom).obj
        ((ModuleCat.extendScalars (algebraMap (Generators.self A B).Ring B)).obj
          (CommRingCat.KaehlerDifferential (polynomial (CommRingCat.of A) B).hom)) :=
  CommRingCat.KaehlerDifferential.map
      ((Category.id_comp (polynomial (CommRingCat.of A) B).hom).trans
        (polynomialIso (CommRingCat.of A) B).hom.w.symm) ≫
    (ModuleCat.restrictScalars
        (polynomialIso (CommRingCat.of A) B).hom.right.hom).map
      (selfNaiveCotangentSpaceUnit A B) ≫
    (ModuleCat.restrictScalarsComp'
      (polynomialIso (CommRingCat.of A) B).hom.right.hom
      (algebraMap (Generators.self A B).Ring B)
      (selfHom (CommRingCat.of A) (under A B)).right.hom
      (selfHom_comp_polynomialIso A B)).inv.app _

/-- Degree-zero comparison of the Under self-presentation differentials with the
extended polynomial Kähler object of `Generators.self`. -/
def selfNaiveDifferentialsMap :
    naiveDifferentials (CommRingCat.of A) (under A B) (under A B).right
        (selfHom (CommRingCat.of A) (under A B)) ⟶
      (ModuleCat.extendScalars (algebraMap (Generators.self A B).Ring B)).obj
        (CommRingCat.KaehlerDifferential (polynomial (CommRingCat.of A) B).hom) :=
  ((ModuleCat.extendRestrictScalarsAdj
      (selfHom (CommRingCat.of A) (under A B)).right.hom).homEquiv _ _).symm
    (selfNaiveDifferentialsRestrict A B)

/-- Inverse restricted comparison from polynomial Kähler differentials to Under
self-presentation differentials. -/
def selfNaiveDifferentialsRestrictInv :
    CommRingCat.KaehlerDifferential (polynomial (CommRingCat.of A) B).hom ⟶
      (ModuleCat.restrictScalars
          (algebraMap (Generators.self A B).Ring B)).obj
        (naiveDifferentials (CommRingCat.of A) (under A B) (under A B).right
          (selfHom (CommRingCat.of A) (under A B))) :=
  CommRingCat.KaehlerDifferential.map
      ((Category.id_comp ((functor (CommRingCat.of A)).obj B).hom).trans
        (polynomialIso (CommRingCat.of A) B).inv.w.symm) ≫
    (ModuleCat.restrictScalars
        (polynomialIso (CommRingCat.of A) B).inv.right.hom).map
      ((ModuleCat.extendRestrictScalarsAdj
          (selfHom (CommRingCat.of A) (under A B)).right.hom).unit.app _) ≫
    (ModuleCat.restrictScalarsComp'
      (polynomialIso (CommRingCat.of A) B).inv.right.hom
      (selfHom (CommRingCat.of A) (under A B)).right.hom
      (algebraMap (Generators.self A B).Ring B)
      (algebraMap_comp_polynomialIso_inv A B)).inv.app _

/-- Inverse degree-zero comparison. -/
def selfNaiveDifferentialsInv :
    (ModuleCat.extendScalars (algebraMap (Generators.self A B).Ring B)).obj
      (CommRingCat.KaehlerDifferential (polynomial (CommRingCat.of A) B).hom) ⟶
      naiveDifferentials (CommRingCat.of A) (under A B) (under A B).right
        (selfHom (CommRingCat.of A) (under A B)) :=
  ((ModuleCat.extendRestrictScalarsAdj
      (algebraMap (Generators.self A B).Ring B)).homEquiv _ _).symm
    (selfNaiveDifferentialsRestrictInv A B)

/-- `selfNaiveDifferentialsMap` is an isomorphism. -/
instance selfNaiveDifferentialsMap_isIso :
    IsIso (selfNaiveDifferentialsMap A B) :=
  sorry

/-- The two degree-zero comparison maps compose to the identity on Under differentials. -/
theorem selfNaiveDifferentialsMap_comp_inv :
    selfNaiveDifferentialsMap A B ≫ selfNaiveDifferentialsInv A B = 𝟙 _ :=
  sorry

/-- Restricted degree `-1` comparison on conormal modules. -/
def selfNaiveConormalRestrictMap :
    naiveConormalRestrict (CommRingCat.of A) (under A B) (under A B).right
        (selfHom (CommRingCat.of A) (under A B)) ⟶
      (ModuleCat.restrictScalars
          (selfHom (CommRingCat.of A) (under A B)).right.hom).obj
        (ModuleCat.of B (Generators.self A B).toExtension.Cotangent) :=
  ConcreteCategory.ofHom
    { toFun := fun x ↦
        Quotient.liftOn x
          (fun i ↦
            Ideal.toCotangent (RingHom.ker (algebraMap (Generators.self A B).Ring B))
              ⟨(polynomialIso (CommRingCat.of A) B).hom.right.hom i.1, sorry⟩)
          (fun _ _ _ ↦ sorry)
      map_add' := sorry
      map_smul' := sorry }

/-- Degree `-1` comparison of the Under self-presentation conormal with the
Generators.self conormal. -/
def selfNaiveConormalMap :
    naiveConormal (CommRingCat.of A) (under A B) (under A B).right
        (selfHom (CommRingCat.of A) (under A B)) ⟶
      ModuleCat.of B (Generators.self A B).toExtension.Cotangent :=
  ((ModuleCat.extendRestrictScalarsAdj
      (selfHom (CommRingCat.of A) (under A B)).right.hom).homEquiv _ _).symm
    (selfNaiveConormalRestrictMap A B)

/-- Inverse degree `-1` comparison. -/
def selfNaiveConormalInv :
    ModuleCat.of B (Generators.self A B).toExtension.Cotangent ⟶
      naiveConormal (CommRingCat.of A) (under A B) (under A B).right
        (selfHom (CommRingCat.of A) (under A B)) :=
  ConcreteCategory.ofHom
    { toFun := fun x ↦
        (1 : (under A B).right) ⊗ₜ[((functor (CommRingCat.of A)).obj
              (under A B).right).right,
            (selfHom (CommRingCat.of A) (under A B)).right.hom]
          (Quotient.liftOn (Extension.Cotangent.val x)
            (fun i ↦
              Ideal.toCotangent
                (RingHom.ker (selfHom (CommRingCat.of A) (under A B)).right.hom)
                ⟨(polynomialIso (CommRingCat.of A) B).inv.right.hom i.1, sorry⟩)
            (fun _ _ _ ↦ sorry))
      map_add' := sorry
      map_smul' := sorry }

/-- `selfNaiveConormalMap` is an isomorphism. -/
instance selfNaiveConormalMap_isIso :
    IsIso (selfNaiveConormalMap A B) :=
  sorry

/-- The two degree `-1` comparison maps compose to the identity. -/
theorem selfNaiveConormalMap_comp_inv :
    selfNaiveConormalMap A B ≫ selfNaiveConormalInv A B = 𝟙 _ :=
  sorry

/-- Components of the forward cochain comparison of `L_{B/A}` with the Under naive
cotangent complex. -/
def selfNaiveIsoCochainHom_f :
    ∀ i : ℤ,
      (selfNaiveComplex (CommRingCat.of A) (under A B)).X i ⟶
        (selfNaiveComplex (CommRingCat.of A) (under A B)).X i
  | Int.ofNat 0 =>
      (naiveComplex_X_zero (CommRingCat.of A) (under A B) (under A B).right
          (selfHom (CommRingCat.of A) (under A B))).hom ≫
        selfNaiveDifferentialsMap A B ≫
          selfNaiveDifferentialsInv A B ≫
            (naiveComplex_X_zero (CommRingCat.of A) (under A B) (under A B).right
                (selfHom (CommRingCat.of A) (under A B))).inv
  | Int.negSucc 0 =>
      (naiveComplex_X_negOne (CommRingCat.of A) (under A B) (under A B).right
          (selfHom (CommRingCat.of A) (under A B))).hom ≫
        selfNaiveConormalMap A B ≫
          selfNaiveConormalInv A B ≫
            (naiveComplex_X_negOne (CommRingCat.of A) (under A B) (under A B).right
                (selfHom (CommRingCat.of A) (under A B))).inv
  | Int.negSucc (_n + 1) => 0
  | Int.ofNat (_n + 1) => 0

/-- Forward cochain comparison on the Under naive cotangent complex, obtained by
transporting along the Under-vs-Generators.self identifications. -/
def selfNaiveIsoCochainHom :
    selfNaiveComplex (CommRingCat.of A) (under A B) ⟶
      selfNaiveComplex (CommRingCat.of A) (under A B) where
  f := selfNaiveIsoCochainHom_f A B
  comm' := sorry

/-- Inverse cochain comparison on the Under naive cotangent complex. -/
def selfNaiveIsoCochainInv :
    selfNaiveComplex (CommRingCat.of A) (under A B) ⟶
      selfNaiveComplex (CommRingCat.of A) (under A B) :=
  selfNaiveIsoCochainHom A B

/-- The two cochain comparisons compose to the identity. -/
theorem selfNaiveIsoCochainHom_comp_inv :
    selfNaiveIsoCochainHom A B ≫ selfNaiveIsoCochainInv A B = 𝟙 _ :=
  sorry

/-- The derived morphism `L_{B/A} ⟶ NL_{B/A}` of the self-presentation, transported
along the Under-vs-Generators.self comparison. -/
def derivedToNaiveObject :
    derived A B ⟶
      DerivedCategory.Q.obj (selfNaiveComplex (CommRingCat.of A) (under A B)) :=
  DerivedCategory.Q.map
    (Algebra.NaiveCotangent.toNaive (CommRingCat.of A) (under A B) ≫
      selfNaiveIsoCochainHom A B)

/-- Unfolding of `derivedToNaiveObject`. -/
theorem derivedToNaiveObject_eq :
    derivedToNaiveObject A B =
      DerivedCategory.Q.map
        (Algebra.NaiveCotangent.toNaive (CommRingCat.of A) (under A B) ≫
          selfNaiveIsoCochainHom A B) :=
  sorry

/-- Lemma 92.11.3 truncation section of the Under self-presentation. -/
def naiveTruncGESection :
    DerivedCategory.Q.obj (selfNaiveComplex (CommRingCat.of A) (under A B)) ⟶
      (t.truncGE (-1)).obj (derived A B) :=
  DerivedCategory.Q.map (selfNaiveIsoCochainInv A B) ≫
    toTruncGE_self (CommRingCat.of A) (under A B)

/-- Unfolding of `naiveTruncGESection`. -/
theorem naiveTruncGESection_eq :
    naiveTruncGESection A B =
      DerivedCategory.Q.map (selfNaiveIsoCochainInv A B) ≫
        toTruncGE_self (CommRingCat.of A) (under A B) :=
  sorry

/-- The chain map `NL_{B/A} ⟶ N[1]` of the Under self-presentation, obtained by
postcomposing the conormal comparison with a Hom representative. -/
def extOneHomUnderChain {N : Type u} [AddCommGroup N] [Module B N]
    (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
    naiveChain (CommRingCat.of A) (under A B) (under A B).right
        (selfHom (CommRingCat.of A) (under A B)) ⟶
      (HomologicalComplex.single (ModuleCat B) (ComplexShape.down ℕ) 1).obj
        (ModuleCat.of B N) :=
  HomologicalComplex.mkHomToSingle
    (selfNaiveConormalMap A B ≫ ModuleCat.ofHom f) sorry

/-- Termwise scalar extension of `toNaive` followed by the explicit comparison, on the
concrete cochain tensor of `L_{B/A}`. -/
def tensorToNaiveTensor (C : Type u) [CommRing C] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C] :
    tensor A B C ⟶
      DerivedCategory.Q.obj
        (((ModuleCat.extendScalars (algebraMap B C)).mapHomologicalComplex (up ℤ)).obj
          (selfNaiveComplex (CommRingCat.of A) (under A B))) :=
  DerivedCategory.Q.map
    (((ModuleCat.extendScalars (algebraMap B C)).mapHomologicalComplex (up ℤ)).map
      (Algebra.NaiveCotangent.toNaive (CommRingCat.of A) (under A B) ≫
        selfNaiveIsoCochainHom A B))

/-- Unfolding of `tensorToNaiveTensor`. -/
theorem tensorToNaiveTensor_eq (C : Type u) [CommRing C] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C] :
    tensorToNaiveTensor A B C =
      DerivedCategory.Q.map
        (((ModuleCat.extendScalars (algebraMap B C)).mapHomologicalComplex (up ℤ)).map
          (Algebra.NaiveCotangent.toNaive (CommRingCat.of A) (under A B) ≫
            selfNaiveIsoCochainHom A B)) :=
  sorry

end SquareZeroExtension

end RingHom
