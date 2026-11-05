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
public import ReasLib.RingTheory.CotangentComplex.NaiveComparison.Explicit
public import ReasLib.RingTheory.CotangentComplex.Transitivity

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
    (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))).right.hom =
      (algebraMap (Generators.self A B).Ring B).comp
        (polynomialIso (CommRingCat.of A) B).hom.right.hom :=
  sorry

/-- Polynomial evaluation is categorical evaluation after `polynomialIso.inv`. -/
theorem algebraMap_comp_polynomialIso_inv :
    (algebraMap (Generators.self A B).Ring B) =
      (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))).right.hom.comp
        (polynomialIso (CommRingCat.of A) B).inv.right.hom :=
  sorry

/-- `polynomialIso` sends the kernel of the categorical counit into the kernel of polynomial
evaluation. -/
theorem polynomialIso_ker_le :
    RingHom.ker (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))).right.hom ≤
      Ideal.comap (polynomialIso (CommRingCat.of A) B).hom.right.hom
        (RingHom.ker (algebraMap (Generators.self A B).Ring B)) := by
  intro x hx
  change (algebraMap (Generators.self A B).Ring B)
    ((polynomialIso (CommRingCat.of A) B).hom.right.hom x) = 0
  change _ = 0 at hx
  exact (RingHom.congr_fun (selfHom_comp_polynomialIso A B) x).symm.trans hx

/-- `polynomialIso.inv` sends the kernel of polynomial evaluation into the kernel of the
categorical counit. -/
theorem polynomialIso_inv_ker_le :
    RingHom.ker (algebraMap (Generators.self A B).Ring B) ≤
      Ideal.comap (polynomialIso (CommRingCat.of A) B).inv.right.hom
        (RingHom.ker (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))).right.hom) := by
  intro x hx
  change (selfHom (CommRingCat.of A)
    (Under.mk (CommRingCat.ofHom (algebraMap A B)))).right.hom
    ((polynomialIso (CommRingCat.of A) B).inv.right.hom x) = 0
  change _ = 0 at hx
  exact (RingHom.congr_fun (algebraMap_comp_polynomialIso_inv A B) x).symm.trans hx

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
          (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))).right.hom).obj
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
      (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))).right.hom
      (selfHom_comp_polynomialIso A B)).inv.app _

/-- Degree-zero comparison of the Under self-presentation differentials with the
extended polynomial Kähler object of `Generators.self`. -/
def selfNaiveDifferentialsMap :
    naiveDifferentials (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))) (Under.mk (CommRingCat.ofHom (algebraMap A B))).right
        (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))) ⟶
      (ModuleCat.extendScalars (algebraMap (Generators.self A B).Ring B)).obj
        (CommRingCat.KaehlerDifferential (polynomial (CommRingCat.of A) B).hom) :=
  ((ModuleCat.extendRestrictScalarsAdj
      (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))).right.hom).homEquiv _ _).symm
    (selfNaiveDifferentialsRestrict A B)

/-- Inverse restricted comparison from polynomial Kähler differentials to Under
self-presentation differentials. -/
def selfNaiveDifferentialsRestrictInv :
    CommRingCat.KaehlerDifferential (polynomial (CommRingCat.of A) B).hom ⟶
      (ModuleCat.restrictScalars
          (algebraMap (Generators.self A B).Ring B)).obj
        (naiveDifferentials (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))) (Under.mk (CommRingCat.ofHom (algebraMap A B))).right
          (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))))) :=
  CommRingCat.KaehlerDifferential.map
      ((Category.id_comp ((functor (CommRingCat.of A)).obj B).hom).trans
        (polynomialIso (CommRingCat.of A) B).inv.w.symm) ≫
    (ModuleCat.restrictScalars
        (polynomialIso (CommRingCat.of A) B).inv.right.hom).map
      ((ModuleCat.extendRestrictScalarsAdj
          (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))).right.hom).unit.app _) ≫
    (ModuleCat.restrictScalarsComp'
      (polynomialIso (CommRingCat.of A) B).inv.right.hom
      (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))).right.hom
      (algebraMap (Generators.self A B).Ring B)
      (algebraMap_comp_polynomialIso_inv A B)).inv.app _

/-- Inverse degree-zero comparison. -/
def selfNaiveDifferentialsInv :
    (ModuleCat.extendScalars (algebraMap (Generators.self A B).Ring B)).obj
      (CommRingCat.KaehlerDifferential (polynomial (CommRingCat.of A) B).hom) ⟶
      naiveDifferentials (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))) (Under.mk (CommRingCat.ofHom (algebraMap A B))).right
        (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))) :=
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

/-- The polynomial comparison on kernel classes respects the conormal quotient relation. -/
theorem selfNaiveConormalRestrictMap_well_defined :
    ∀ i j, (naiveKerSquare (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))) (Under.mk (CommRingCat.ofHom (algebraMap A B))).right
        (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))))).quotientRel i j →
      (fun i ↦
          Extension.Cotangent.of (P := (Generators.self A B).toExtension)
            (Ideal.toCotangent (RingHom.ker (algebraMap (Generators.self A B).Ring B))
              ⟨(polynomialIso (CommRingCat.of A) B).hom.right.hom i.1,
                polynomialIso_ker_le A B i.2⟩)) i = (fun i ↦
          Extension.Cotangent.of (P := (Generators.self A B).toExtension)
            (Ideal.toCotangent (RingHom.ker (algebraMap (Generators.self A B).Ring B))
              ⟨(polynomialIso (CommRingCat.of A) B).hom.right.hom i.1,
                polynomialIso_ker_le A B i.2⟩)) j := sorry

/-- The quotient comparison of conormal modules preserves addition. -/
theorem selfNaiveConormalRestrictMap_map_add :
    let f : naiveConormalRestrict (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))) (Under.mk (CommRingCat.ofHom (algebraMap A B))).right
        (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))) → (ModuleCat.restrictScalars
          (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))).right.hom).obj
        (ModuleCat.of B (Generators.self A B).toExtension.Cotangent) := fun x ↦ Quotient.liftOn x
      (fun i ↦ Extension.Cotangent.of (P := (Generators.self A B).toExtension)
        (Ideal.toCotangent (RingHom.ker (algebraMap (Generators.self A B).Ring B))
          ⟨(polynomialIso (CommRingCat.of A) B).hom.right.hom i.1,
            polynomialIso_ker_le A B i.2⟩))
      (selfNaiveConormalRestrictMap_well_defined A B)
    ∀ x y, f (x + y) = f x + f y := sorry

/-- The quotient comparison of conormal modules preserves scalar multiplication. -/
theorem selfNaiveConormalRestrictMap_map_smul :
    let f : naiveConormalRestrict (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))) (Under.mk (CommRingCat.ofHom (algebraMap A B))).right
        (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))) → (ModuleCat.restrictScalars
          (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))).right.hom).obj
        (ModuleCat.of B (Generators.self A B).toExtension.Cotangent) := fun x ↦ Quotient.liftOn x
      (fun i ↦ Extension.Cotangent.of (P := (Generators.self A B).toExtension)
        (Ideal.toCotangent (RingHom.ker (algebraMap (Generators.self A B).Ring B))
          ⟨(polynomialIso (CommRingCat.of A) B).hom.right.hom i.1,
            polynomialIso_ker_le A B i.2⟩))
      (selfNaiveConormalRestrictMap_well_defined A B)
    ∀ (r : ((functor (CommRingCat.of A)).obj (Under.mk (CommRingCat.ofHom (algebraMap A B))).right).right) x,
      f (r • x) = r • f x := sorry

/-- The restricted comparison from the categorical conormal to the polynomial conormal. -/
def selfNaiveConormalRestrictMap :
    naiveConormalRestrict (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))) (Under.mk (CommRingCat.ofHom (algebraMap A B))).right
        (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))) ⟶ (ModuleCat.restrictScalars
          (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))).right.hom).obj
        (ModuleCat.of B (Generators.self A B).toExtension.Cotangent) :=
  ConcreteCategory.ofHom
    { toFun := fun x ↦ Quotient.liftOn x (fun i ↦
          Extension.Cotangent.of (P := (Generators.self A B).toExtension)
            (Ideal.toCotangent (RingHom.ker (algebraMap (Generators.self A B).Ring B))
              ⟨(polynomialIso (CommRingCat.of A) B).hom.right.hom i.1,
                polynomialIso_ker_le A B i.2⟩))
          (selfNaiveConormalRestrictMap_well_defined A B)
      map_add' := selfNaiveConormalRestrictMap_map_add A B
      map_smul' := selfNaiveConormalRestrictMap_map_smul A B }

/-- Degree `-1` comparison of the Under self-presentation conormal with the
Generators.self conormal. -/
def selfNaiveConormalMap :
    naiveConormal (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))) (Under.mk (CommRingCat.ofHom (algebraMap A B))).right
        (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))) ⟶
      ModuleCat.of B (Generators.self A B).toExtension.Cotangent :=
  ((ModuleCat.extendRestrictScalarsAdj
      (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))).right.hom).homEquiv _ _).symm
    (selfNaiveConormalRestrictMap A B)

/-- The inverse polynomial comparison respects the conormal quotient relation. -/
theorem selfNaiveConormalInv_well_defined :
    ∀ i j,
      ((RingHom.ker (algebraMap (Generators.self A B).Ring B)) •
        (⊤ : Submodule (Generators.self A B).Ring
          (RingHom.ker (algebraMap (Generators.self A B).Ring B)))).quotientRel i j →
      (fun i ↦
          Ideal.toCotangent
            (RingHom.ker (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))).right.hom)
            ⟨(polynomialIso (CommRingCat.of A) B).inv.right.hom i.1,
              polynomialIso_inv_ker_le A B i.2⟩) i = (fun i ↦
          Ideal.toCotangent
            (RingHom.ker (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))).right.hom)
            ⟨(polynomialIso (CommRingCat.of A) B).inv.right.hom i.1,
              polynomialIso_inv_ker_le A B i.2⟩) j := sorry

/-- The inverse conormal comparison preserves addition. -/
theorem selfNaiveConormalInv_map_add :
    let f : (Generators.self A B).toExtension.Cotangent → naiveConormal (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))) (Under.mk (CommRingCat.ofHom (algebraMap A B))).right
        (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))) := fun x ↦ (1 : (Under.mk (CommRingCat.ofHom (algebraMap A B))).right) ⊗ₜ[((functor (CommRingCat.of A)).obj
              (Under.mk (CommRingCat.ofHom (algebraMap A B))).right).right,
            (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))).right.hom]
      (Quotient.liftOn (Extension.Cotangent.val x)
        (fun i ↦ Ideal.toCotangent
          (RingHom.ker (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))).right.hom)
          ⟨(polynomialIso (CommRingCat.of A) B).inv.right.hom i.1,
            polynomialIso_inv_ker_le A B i.2⟩)
        (selfNaiveConormalInv_well_defined A B))
    ∀ x y, f (x + y) = f x + f y := sorry

/-- The inverse conormal comparison preserves scalar multiplication. -/
theorem selfNaiveConormalInv_map_smul :
    let f : (Generators.self A B).toExtension.Cotangent → naiveConormal (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))) (Under.mk (CommRingCat.ofHom (algebraMap A B))).right
        (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))) := fun x ↦ (1 : (Under.mk (CommRingCat.ofHom (algebraMap A B))).right) ⊗ₜ[((functor (CommRingCat.of A)).obj
              (Under.mk (CommRingCat.ofHom (algebraMap A B))).right).right,
            (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))).right.hom]
      (Quotient.liftOn (Extension.Cotangent.val x)
        (fun i ↦ Ideal.toCotangent
          (RingHom.ker (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))).right.hom)
          ⟨(polynomialIso (CommRingCat.of A) B).inv.right.hom i.1,
            polynomialIso_inv_ker_le A B i.2⟩)
        (selfNaiveConormalInv_well_defined A B))
    ∀ (r : B) x,
      f (r • x) = @SMul.smul _ _ (naiveConormal (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))
        (Under.mk (CommRingCat.ofHom (algebraMap A B))).right
        (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))))).isModule.toSMul r (f x) := sorry

/-- The inverse comparison from the polynomial conormal to the categorical conormal. -/
def selfNaiveConormalInv :
    ModuleCat.of B (Generators.self A B).toExtension.Cotangent ⟶
      naiveConormal (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))) (Under.mk (CommRingCat.ofHom (algebraMap A B))).right
        (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))) :=
  ConcreteCategory.ofHom
    { toFun := fun x ↦ (1 : (Under.mk (CommRingCat.ofHom (algebraMap A B))).right) ⊗ₜ[((functor (CommRingCat.of A)).obj
              (Under.mk (CommRingCat.ofHom (algebraMap A B))).right).right,
            (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))).right.hom]
          (Quotient.liftOn (Extension.Cotangent.val x) (fun i ↦
          Ideal.toCotangent
            (RingHom.ker (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))).right.hom)
            ⟨(polynomialIso (CommRingCat.of A) B).inv.right.hom i.1,
              polynomialIso_inv_ker_le A B i.2⟩)
            (selfNaiveConormalInv_well_defined A B))
      map_add' := selfNaiveConormalInv_map_add A B
      map_smul' := selfNaiveConormalInv_map_smul A B }

/-- `selfNaiveConormalMap` is an isomorphism. -/
instance selfNaiveConormalMap_isIso :
    IsIso (selfNaiveConormalMap A B) :=
  sorry

/-- The two degree `-1` comparison maps compose to the identity. -/
theorem selfNaiveConormalMap_comp_inv :
    selfNaiveConormalMap A B ≫ selfNaiveConormalInv A B = 𝟙 _ :=
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- The scalar-extended polynomial Kähler object is the cotangent space of the
canonical self-presentation. Both maps are the identity on tensors. -/
def selfNaiveCotangentSpaceIso :
    (ModuleCat.extendScalars (algebraMap (Generators.self A B).Ring B)).obj
      (CommRingCat.KaehlerDifferential (polynomial (CommRingCat.of A) B).hom) ≅
        ModuleCat.of B (Generators.self A B).toExtension.CotangentSpace :=
  by
    change
      (letI := (algebraMap A (Generators.self A B).Ring).toAlgebra
       letI := (algebraMap (Generators.self A B).Ring B).toAlgebra
       ModuleCat.of B (B ⊗[(Generators.self A B).Ring]
         Ω[(Generators.self A B).Ring⁄A])) ≅
        ModuleCat.of B (Generators.self A B).toExtension.CotangentSpace
    let F (a : Algebra A (Generators.self A B).Ring)
        (b : Algebra (Generators.self A B).Ring B) : ModuleCat B :=
      letI := a
      letI := b
      ModuleCat.of B (B ⊗[(Generators.self A B).Ring]
        Ω[(Generators.self A B).Ring⁄A])
    exact eqToIso (congrArg₂ F
      (toAlgebra_algebraMap (R := A) (S := (Generators.self A B).Ring))
      (toAlgebra_algebraMap (R := (Generators.self A B).Ring) (S := B)))

/-- Components of the comparison with the shared canonical naive complex. -/
def selfNaiveIsoCochainHom_f :
    ∀ i : ℤ, (selfNaiveComplex (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))).X i ⟶ ((Algebra.naiveCotangent A B).extend embeddingDownNat).X i
  | Int.ofNat 0 =>
      (naiveComplex_X_zero (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))) (Under.mk (CommRingCat.ofHom (algebraMap A B))).right
          (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))))).hom ≫
        selfNaiveDifferentialsMap A B ≫ (selfNaiveCotangentSpaceIso A B).hom ≫
          ((Algebra.naiveCotangent A B).extendXIso embeddingDownNat
            (rfl : embeddingDownNat.f 0 = 0)).inv
  | Int.negSucc 0 =>
      (naiveComplex_X_negOne (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))) (Under.mk (CommRingCat.ofHom (algebraMap A B))).right
          (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))))).hom ≫
        selfNaiveConormalMap A B ≫
          ModuleCat.ofHom (Extension.NaiveCotangent.liftEquiv
            (Generators.self A B).toExtension).symm.toLinearMap ≫
          ((Algebra.naiveCotangent A B).extendXIso embeddingDownNat
            (rfl : embeddingDownNat.f 1 = -1)).inv
  | Int.negSucc (_ + 1) => 0
  | Int.ofNat (_ + 1) => 0

/-- The polynomial kernel and differential identifications respect the differential
of the shared complex (in particular its lifted conormal term). -/
theorem selfNaiveIsoCochainHom_comm (i j : ℤ) (h : (up ℤ).Rel i j) :
    selfNaiveIsoCochainHom_f A B i ≫ ((Algebra.naiveCotangent A B).extend embeddingDownNat).d i j =
      (selfNaiveComplex (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))).d i j ≫ selfNaiveIsoCochainHom_f A B j := sorry

/-- The actual Under-to-canonical comparison, with polynomial differential and
kernel maps in degrees zero and minus one. -/
def selfNaiveIsoCochainHom :
    selfNaiveComplex (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))) ⟶ ((Algebra.naiveCotangent A B).extend embeddingDownNat) where
  f := selfNaiveIsoCochainHom_f A B
  comm' := selfNaiveIsoCochainHom_comm A B

/-- Components of the explicit reverse comparison. -/
def selfNaiveIsoCochainInv_f :
    ∀ i : ℤ, ((Algebra.naiveCotangent A B).extend embeddingDownNat).X i ⟶ (selfNaiveComplex (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))).X i
  | Int.ofNat 0 =>
      ((Algebra.naiveCotangent A B).extendXIso embeddingDownNat
        (rfl : embeddingDownNat.f 0 = 0)).hom ≫
      (selfNaiveCotangentSpaceIso A B).inv ≫ selfNaiveDifferentialsInv A B ≫
        (naiveComplex_X_zero (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))) (Under.mk (CommRingCat.ofHom (algebraMap A B))).right
          (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))))).inv
  | Int.negSucc 0 =>
      ((Algebra.naiveCotangent A B).extendXIso embeddingDownNat
        (rfl : embeddingDownNat.f 1 = -1)).hom ≫
      ModuleCat.ofHom (Extension.NaiveCotangent.liftEquiv
        (Generators.self A B).toExtension).toLinearMap ≫
      selfNaiveConormalInv A B ≫ (naiveComplex_X_negOne (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))) (Under.mk (CommRingCat.ofHom (algebraMap A B))).right
          (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))))).inv
  | Int.negSucc (_ + 1) => 0
  | Int.ofNat (_ + 1) => 0

set_option backward.isDefEq.respectTransparency false in
/-- The Under model vanishes outside its two displayed degrees. -/
private theorem selfNaiveUnder_isZero (i : ℤ) (h0 : i ≠ 0) (h1 : i ≠ -1) :
    CategoryTheory.Limits.IsZero
      ((selfNaiveComplex (CommRingCat.of A)
        (Under.mk (CommRingCat.ofHom (algebraMap A B)))).X i) := by
  cases i with
  | ofNat n =>
    cases n with
    | zero => exact (h0 rfl).elim
    | succ n =>
      apply HomologicalComplex.isZero_extend_X
      intro k hk
      change -(k : ℤ) = (n : ℤ) + 1 at hk
      omega
  | negSucc n =>
    cases n with
    | zero => exact (h1 rfl).elim
    | succ n =>
      let K := naiveChain (CommRingCat.of A)
        (Under.mk (CommRingCat.ofHom (algebraMap A B))) B
        (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))))
      apply CategoryTheory.Limits.IsZero.of_iso _
        (K.extendXIso embeddingDownNat (rfl : embeddingDownNat.f (n + 2) = _))
      exact (CategoryTheory.Limits.isZero_zero (ModuleCat B)).of_iso
        (ChainComplex.mk'XIso _ _ _ _ n)

set_option backward.isDefEq.respectTransparency false in
/-- The shared model vanishes outside its two displayed degrees. -/
private theorem selfNaiveCanonical_isZero (i : ℤ) (h0 : i ≠ 0) (h1 : i ≠ -1) :
    CategoryTheory.Limits.IsZero
      (((Algebra.naiveCotangent A B).extend embeddingDownNat).X i) := by
  cases i with
  | ofNat n =>
    cases n with
    | zero => exact (h0 rfl).elim
    | succ n =>
      apply HomologicalComplex.isZero_extend_X
      intro k hk
      change -(k : ℤ) = (n : ℤ) + 1 at hk
      omega
  | negSucc n =>
    cases n with
    | zero => exact (h1 rfl).elim
    | succ n =>
      apply CategoryTheory.Limits.IsZero.of_iso _
        ((Algebra.naiveCotangent A B).extendXIso embeddingDownNat
          (rfl : embeddingDownNat.f (n + 2) = _))
      exact (ModuleCat.isZero_of_subsingleton (ModuleCat.of B PUnit)).of_iso
        (Extension.NaiveCotangent.componentSuccSuccIsoUnit
          (Generators.self A B).toExtension n)

set_option backward.isDefEq.respectTransparency false in
/-- The explicit reverse components undo the forward components. -/
private theorem selfNaiveIsoCochainHom_f_comp_inv_f (i : ℤ) :
    selfNaiveIsoCochainHom_f A B i ≫ selfNaiveIsoCochainInv_f A B i = 𝟙 _ := by
  by_cases h0 : i = 0
  · subst i
    simp only [selfNaiveIsoCochainHom_f, selfNaiveIsoCochainInv_f,
      Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc (selfNaiveDifferentialsMap A B),
      selfNaiveDifferentialsMap_comp_inv]
    simp only [Category.id_comp, Iso.hom_inv_id]
  by_cases h1 : i = -1
  · subst i
    let U : CochainComplex (ModuleCat B) ℤ := selfNaiveComplex (CommRingCat.of A)
      (Under.mk (CommRingCat.ofHom (algebraMap A B)))
    let e := (Extension.NaiveCotangent.liftEquiv (Generators.self A B).toExtension).toModuleIso
    let u : U.X (-1) ≅ (show ModuleCat B from naiveConormal (CommRingCat.of A)
        (Under.mk (CommRingCat.ofHom (algebraMap A B))) B
        (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))))) :=
      naiveComplex_X_negOne (CommRingCat.of A)
        (Under.mk (CommRingCat.ofHom (algebraMap A B))) B
        (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))))
    let c := (Algebra.naiveCotangent A B).extendXIso embeddingDownNat
      (rfl : embeddingDownNat.f 1 = -1)
    change (u.hom ≫ selfNaiveConormalMap A B ≫ e.inv ≫ c.inv) ≫
      (c.hom ≫ e.hom ≫ selfNaiveConormalInv A B ≫ u.inv) = 𝟙 _
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    erw [← Category.assoc (selfNaiveConormalMap A B), selfNaiveConormalMap_comp_inv]
    simp only [Category.id_comp, Iso.hom_inv_id]
  exact (selfNaiveUnder_isZero A B i h0 h1).eq_of_src _ _

set_option backward.isDefEq.respectTransparency false in
/-- The reverse polynomial identifications respect the differential. -/
theorem selfNaiveIsoCochainInv_comm (i j : ℤ) (h : (up ℤ).Rel i j) :
    selfNaiveIsoCochainInv_f A B i ≫ (selfNaiveComplex (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))).d i j =
      ((Algebra.naiveCotangent A B).extend embeddingDownNat).d i j ≫ selfNaiveIsoCochainInv_f A B j := by
  have hi : Epi (selfNaiveIsoCochainHom_f A B i) := by
    by_cases h0 : i = 0
    · subst i
      dsimp only [selfNaiveIsoCochainHom_f]
      infer_instance
    by_cases h1 : i = -1
    · subst i
      dsimp only [selfNaiveIsoCochainHom_f]
      haveI : IsIso (show (show ModuleCat B from naiveConormal (CommRingCat.of A)
          (Under.mk (CommRingCat.ofHom (algebraMap A B))) B
          (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))))) ⟶
          ModuleCat.of B (Generators.self A B).toExtension.Cotangent from
          selfNaiveConormalMap A B) := selfNaiveConormalMap_isIso A B
      change Epi (_ ≫ _ ≫ ((Extension.NaiveCotangent.liftEquiv
        (Generators.self A B).toExtension).toModuleIso).inv ≫ _)
      infer_instance
    exact (selfNaiveCanonical_isZero A B i h0 h1).epi _
  apply (cancel_epi (selfNaiveIsoCochainHom_f A B i)).1
  rw [← Category.assoc, selfNaiveIsoCochainHom_f_comp_inv_f, Category.id_comp,
    ← Category.assoc, selfNaiveIsoCochainHom_comm A B i j h,
    Category.assoc, selfNaiveIsoCochainHom_f_comp_inv_f, Category.comp_id]

/-- Explicit inverse comparison from the shared canonical model to the Under model. -/
def selfNaiveIsoCochainInv :
    ((Algebra.naiveCotangent A B).extend embeddingDownNat) ⟶ selfNaiveComplex (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))) where
  f := selfNaiveIsoCochainInv_f A B
  comm' := selfNaiveIsoCochainInv_comm A B

set_option backward.isDefEq.respectTransparency false in
/-- The two cochain comparisons compose to the identity. -/
private theorem selfNaiveIsoCochainHom_comp_inv :
    selfNaiveIsoCochainHom A B ≫ selfNaiveIsoCochainInv A B = 𝟙 _ := by
  ext i : 1
  exact selfNaiveIsoCochainHom_f_comp_inv_f A B i

/-- The degree minus one differential square compares the genuine two models. -/
theorem selfNaiveIsoCochainHom_d_negOne_zero :
    (selfNaiveIsoCochainHom A B).f (-1) ≫ ((Algebra.naiveCotangent A B).extend embeddingDownNat).d (-1) 0 =
      (selfNaiveComplex (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))).d (-1) 0 ≫ (selfNaiveIsoCochainHom A B).f 0 :=
  (selfNaiveIsoCochainHom A B).comm (-1) 0

/-- The derived morphism `L_{B/A} ⟶ NL_{B/A}` of the self-presentation, transported
along the Under-vs-Generators.self comparison. -/
def derivedToNaiveObject :
    derived A B ⟶ Algebra.naiveCotangentObject A B :=
  DerivedCategory.Q.map
    (Algebra.NaiveCotangent.toNaive (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))) ≫
      selfNaiveIsoCochainHom A B)

/-- Unfolding of `derivedToNaiveObject`. -/
theorem derivedToNaiveObject_eq :
    derivedToNaiveObject A B =
      DerivedCategory.Q.map
        (Algebra.NaiveCotangent.toNaive (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))) ≫
          selfNaiveIsoCochainHom A B) :=
  rfl

/-- The section identifying the naive complex with the truncation in degrees at least minus one. -/
def naiveTruncGESection :
    Algebra.naiveCotangentObject A B ⟶
      (t.truncGE (-1)).obj (derived A B) :=
  DerivedCategory.Q.map (selfNaiveIsoCochainInv A B) ≫
    toTruncGE_self (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))

/-- Unfolding of `naiveTruncGESection`. -/
theorem naiveTruncGESection_eq :
    naiveTruncGESection A B =
      DerivedCategory.Q.map (selfNaiveIsoCochainInv A B) ≫
        toTruncGE_self (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The shared comparison followed by the explicit section is the canonical
truncation projection. This is the source-facing comparison of tag `08RB`. -/
theorem derivedToNaiveObject_comp_naiveTruncGESection :
    derivedToNaiveObject A B ≫ naiveTruncGESection A B =
      (t.truncGEπ (-1)).app (derived A B) := by
  let U : CochainComplex (ModuleCat B) ℤ := selfNaiveComplex (CommRingCat.of A)
    (Under.mk (CommRingCat.ofHom (algebraMap A B)))
  let a : derived A B ⟶ DerivedCategory.Q.obj U := DerivedCategory.Q.map
    (Algebra.NaiveCotangent.toNaive (CommRingCat.of A)
      (Under.mk (CommRingCat.ofHom (algebraMap A B))))
  let s : DerivedCategory.Q.obj U ⟶ (t.truncGE (-1)).obj (derived A B) :=
    toTruncGE_self (CommRingCat.of A)
      (Under.mk (CommRingCat.ofHom (algebraMap A B)))
  haveI : IsIso s := Algebra.NaiveCotangent.toTruncGE_self_isIso
    (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))
  have ha : (t.truncGE (-1)).map a =
      inv s ≫ (t.truncGEπ (-1)).app (DerivedCategory.Q.obj U) :=
    Algebra.NaiveCotangent.toNaive_inv_toTruncGE_self (CommRingCat.of A)
      (Under.mk (CommRingCat.ofHom (algebraMap A B)))
  calc
    derivedToNaiveObject A B ≫ naiveTruncGESection A B = a ≫ s := by
      dsimp only [derivedToNaiveObject, naiveTruncGESection, a, s]
      rw [Functor.map_comp, Category.assoc, ← Category.assoc
        (DerivedCategory.Q.map (selfNaiveIsoCochainHom A B)),
        ← Functor.map_comp, selfNaiveIsoCochainHom_comp_inv,
        CategoryTheory.Functor.map_id, Category.id_comp]
    _ = (t.truncGEπ (-1)).app (derived A B) := by
      apply (cancel_mono ((t.truncGEπ (-1)).app
        ((t.truncGE (-1)).obj (derived A B)))).1
      calc
        (a ≫ s) ≫ (t.truncGEπ (-1)).app ((t.truncGE (-1)).obj (derived A B)) =
            a ≫ (t.truncGEπ (-1)).app (DerivedCategory.Q.obj U) ≫
              (t.truncGE (-1)).map s := by
          rw [Category.assoc, ← t.truncGEπ_naturality (-1) s]
        _ = (t.truncGEπ (-1)).app (derived A B) ≫ (t.truncGE (-1)).map a ≫
            (t.truncGE (-1)).map s := by
          rw [← t.truncGEπ_naturality_assoc (-1) a]
        _ = (t.truncGEπ (-1)).app (derived A B) ≫ inv s ≫
            (t.truncGEπ (-1)).app (DerivedCategory.Q.obj U) ≫
              (t.truncGE (-1)).map s := by
          rw [ha, Category.assoc]
        _ = (t.truncGEπ (-1)).app (derived A B) ≫ inv s ≫ s ≫
            (t.truncGEπ (-1)).app ((t.truncGE (-1)).obj (derived A B)) := by
          rw [t.truncGEπ_naturality (-1) s]
        _ = (t.truncGEπ (-1)).app (derived A B) ≫
            (t.truncGEπ (-1)).app ((t.truncGE (-1)).obj (derived A B)) := by
          simp only [IsIso.inv_hom_id_assoc]

/-- A conormal functional annihilates the incoming differential in the naive chain complex. -/
theorem extOneHomUnderChain_d_comp {N : Type u} [AddCommGroup N] [Module B N]
    (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N)
    (i : ℕ) (h : (ComplexShape.down ℕ).Rel i 1) :
    (naiveChain (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))) (Under.mk (CommRingCat.ofHom (algebraMap A B))).right
        (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))))).d i 1 ≫
      (selfNaiveConormalMap A B ≫ ModuleCat.ofHom f) = 0 := sorry

/-- The chain map `NL_{B/A} ⟶ N[1]` of the Under self-presentation, obtained by
postcomposing the conormal comparison with a Hom representative. -/
def extOneHomUnderChain {N : Type u} [AddCommGroup N] [Module B N]
    (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
    naiveChain (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))) (Under.mk (CommRingCat.ofHom (algebraMap A B))).right
        (selfHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))) ⟶
      (HomologicalComplex.single (ModuleCat B) (ComplexShape.down ℕ) 1).obj
        (ModuleCat.of B N) :=
  HomologicalComplex.mkHomToSingle
    (selfNaiveConormalMap A B ≫ ModuleCat.ofHom f) (extOneHomUnderChain_d_comp A B f)

/-- Termwise scalar extension of `toNaive` followed by the explicit comparison, on the
concrete cochain tensor of `L_{B/A}`. -/
def tensorToNaiveTensor (C : Type u) [CommRing C] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C] :
    tensor A B C ⟶
      DerivedCategory.Q.obj
        (((ModuleCat.extendScalars (algebraMap B C)).mapHomologicalComplex (up ℤ)).obj
          (selfNaiveComplex (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))))) :=
  DerivedCategory.Q.map
    (((ModuleCat.extendScalars (algebraMap B C)).mapHomologicalComplex (up ℤ)).map
      (Algebra.NaiveCotangent.toNaive (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))) ≫
        selfNaiveIsoCochainHom A B ≫ selfNaiveIsoCochainInv A B))

/-- Unfolding of `tensorToNaiveTensor`. -/
theorem tensorToNaiveTensor_eq (C : Type u) [CommRing C] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C] :
    tensorToNaiveTensor A B C =
      DerivedCategory.Q.map
        (((ModuleCat.extendScalars (algebraMap B C)).mapHomologicalComplex (up ℤ)).map
          (Algebra.NaiveCotangent.toNaive (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))) ≫
            selfNaiveIsoCochainHom A B ≫ selfNaiveIsoCochainInv A B)) :=
  rfl

end SquareZeroExtension

end RingHom
