/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CotangentComplex.Basic
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# Degree-zero homology of cotangent complexes

The canonical augmentation of the standard-resolution cotangent complex identifies its
zeroth cohomology with the module of Kähler differentials. The inverse is induced by the
homology classes of differentials of universal free-algebra generators.
-/

@[expose] public section

open CategoryTheory
open HomologicalComplex
open Opposite
open AlgebraicTopology
open scoped Simplicial

noncomputable section

universe u

namespace CategoryTheory.CommRingCat.Under
namespace CotangentComplex

/-- The Kähler base-change map `Ω_{P_0/A} ⊗_{P_0} B ⟶ Ω_{B/A}` along the
standard-resolution augmentation. -/
def standardToKaehler (A : CommRingCat.{u}) (B : Under A) :
    (simplicialModule A B).obj (op ⦋0⦌) ⟶ CommRingCat.KaehlerDifferential B.hom :=
  ((ModuleCat.extendRestrictScalarsAdj
      (standardAugmentation A B (op ⦋0⦌)).hom).homEquiv _ _).symm
    (CommRingCat.KaehlerDifferential.map
      ((Category.id_comp B.hom).trans
        (((PolynomialResolution.evaluation A).obj B).hom.app (op ⦋0⦌)).w.symm))

set_option backward.isDefEq.respectTransparency false in
private theorem standardToKaehler_unit_d (A : CommRingCat.{u}) (B : Under A)
    (x : (standardTerm A B (op ⦋0⦌)).right) :
    standardToKaehler A B
      (((ModuleCat.extendRestrictScalarsAdj
        (standardAugmentation A B (op ⦋0⦌)).hom).unit.app
          (CommRingCat.KaehlerDifferential (standardTerm A B (op ⦋0⦌)).hom))
          (CommRingCat.KaehlerDifferential.d x)) =
      CommRingCat.KaehlerDifferential.d (standardAugmentation A B (op ⦋0⦌) x) := by
  change ((ModuleCat.extendRestrictScalarsAdj
    (standardAugmentation A B (op ⦋0⦌)).hom).homEquiv _ _
      (standardToKaehler A B)) (CommRingCat.KaehlerDifferential.d x) = _
  simp only [standardToKaehler, Equiv.apply_symm_apply, CommRingCat.KaehlerDifferential.map_d]

set_option backward.isDefEq.respectTransparency false in
private theorem simplicialModuleMap_unit_d (A : CommRingCat.{u}) (B : Under A)
    {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) (x : (standardTerm A B n).right) :
    simplicialModuleMap A B φ
      (((ModuleCat.extendRestrictScalarsAdj (standardAugmentation A B n).hom).unit.app
        (CommRingCat.KaehlerDifferential (standardTerm A B n).hom))
        (CommRingCat.KaehlerDifferential.d x)) =
      ((ModuleCat.extendRestrictScalarsAdj (standardAugmentation A B m).hom).unit.app
        (CommRingCat.KaehlerDifferential (standardTerm A B m).hom))
        (CommRingCat.KaehlerDifferential.d ((standardMap A B φ).right x)) := by
  change ((ModuleCat.extendRestrictScalarsAdj
    (standardAugmentation A B n).hom).homEquiv _ _
      (simplicialModuleMap A B φ)) (CommRingCat.KaehlerDifferential.d x) = _
  simp only [simplicialModuleMap, Equiv.apply_symm_apply, ModuleCat.comp_apply,
    ModuleCat.restrictScalars.map_apply, simplicialDifferentialsMap,
    CommRingCat.KaehlerDifferential.map_d]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem generator_augmentation (A : CommRingCat.{u}) (B : Under A) (b : B.right) :
    standardAugmentation A B (op ⦋0⦌)
      ((eqToHom (PolynomialResolution.evaluation.obj_eq A B 0).symm).right
        (CommRingCat.Under.FreeAlgebra.generator A b)) = b := by
  change ((CommRingCat.Under.FreeAlgebra.adjunction A).counit.app B).right
    (CommRingCat.Under.FreeAlgebra.generator A b) = b
  exact congrArg (fun f ↦ f b)
    ((CommRingCat.Under.FreeAlgebra.adjunction A).right_triangle_components B)

set_option backward.isDefEq.respectTransparency false in
private theorem faces_comp_standardToKaehler (A : CommRingCat.{u}) (B : Under A)
    (φ ψ : op ⦋1⦌ ⟶ op ⦋0⦌) :
    simplicialModuleMap A B φ ≫ standardToKaehler A B =
      simplicialModuleMap A B ψ ≫ standardToKaehler A B := by
  apply ((ModuleCat.extendRestrictScalarsAdj
    (standardAugmentation A B (op ⦋1⦌)).hom).homEquiv _ _).injective
  apply CommRingCat.KaehlerDifferential.ext
  intro x
  change standardToKaehler A B (simplicialModuleMap A B φ
    (((ModuleCat.extendRestrictScalarsAdj
      (standardAugmentation A B (op ⦋1⦌)).hom).unit.app _)
        (CommRingCat.KaehlerDifferential.d x))) =
    standardToKaehler A B (simplicialModuleMap A B ψ
    (((ModuleCat.extendRestrictScalarsAdj
      (standardAugmentation A B (op ⦋1⦌)).hom).unit.app _)
        (CommRingCat.KaehlerDifferential.d x)))
  rw [simplicialModuleMap_unit_d, standardToKaehler_unit_d,
    simplicialModuleMap_unit_d, standardToKaehler_unit_d]
  apply congrArg (fun b ↦ (CommRingCat.KaehlerDifferential.d b :
    CommRingCat.KaehlerDifferential B.hom))
  exact (congrArg (fun f ↦ f x) (standardMap_comp_augmentation A B φ)).trans
    (congrArg (fun f ↦ f x) (standardMap_comp_augmentation A B ψ)).symm

set_option backward.isDefEq.respectTransparency false in
private theorem face_zero_generator (A : CommRingCat.{u}) (B : Under A)
    (p : (standardTerm A B (op ⦋0⦌)).right) :
    (standardMap A B (SimplexCategory.δ (0 : Fin 2)).op).right
      ((eqToHom (PolynomialResolution.evaluation.obj_eq A B 1).symm).right
        (CommRingCat.Under.FreeAlgebra.generator A p)) =
      (eqToHom (PolynomialResolution.evaluation.obj_eq A B 0).symm).right
        (CommRingCat.Under.FreeAlgebra.generator A
          (standardAugmentation A B (op ⦋0⦌) p)) := by
  change (((PolynomialResolution.comonad A).simplicialResolution.δ (0 : Fin 2)).app B).right
    (CommRingCat.Under.FreeAlgebra.generator A p) = _
  rw [Comonad.simplicialResolution.face]
  change ((CommRingCat.Under.FreeAlgebra.functor A).map
    ((CommRingCat.Under.FreeAlgebra.carrier A).map
      ((CommRingCat.Under.FreeAlgebra.adjunction A).counit.app B))).right
        (CommRingCat.Under.FreeAlgebra.generator A p) = _
  exact (congrArg (fun f ↦ f p)
    ((CommRingCat.Under.FreeAlgebra.adjunction A).unit.naturality
      ((CommRingCat.Under.FreeAlgebra.carrier A).map
        ((CommRingCat.Under.FreeAlgebra.adjunction A).counit.app B)))).symm

set_option backward.isDefEq.respectTransparency false in
private theorem face_one_generator (A : CommRingCat.{u}) (B : Under A)
    (p : (standardTerm A B (op ⦋0⦌)).right) :
    (standardMap A B (SimplexCategory.δ (1 : Fin 2)).op).right
      ((eqToHom (PolynomialResolution.evaluation.obj_eq A B 1).symm).right
        (CommRingCat.Under.FreeAlgebra.generator A p)) = p := by
  change (((PolynomialResolution.comonad A).simplicialResolution.δ (1 : Fin 2)).app B).right
    (CommRingCat.Under.FreeAlgebra.generator A p) = p
  rw [Comonad.simplicialResolution.face]
  change ((CommRingCat.Under.FreeAlgebra.adjunction A).counit.app
    ((CommRingCat.Under.FreeAlgebra.comonadFunctor A).obj B)).right
    (CommRingCat.Under.FreeAlgebra.generator A p) = p
  exact congrArg (fun f ↦ f p)
    ((CommRingCat.Under.FreeAlgebra.adjunction A).right_triangle_components _)

end CotangentComplex
end CategoryTheory.CommRingCat.Under

namespace Algebra.CotangentComplex

open CommRingCat.Under.CotangentComplex

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- The comparison from the categorical Kähler module of `algebraMap A B` to the
ambient module of Kähler differentials `Ω[B⁄A]`. -/
def kaehlerOfAlgebraMap :
    CommRingCat.KaehlerDifferential (CommRingCat.ofHom (algebraMap A B)) ⟶
      ModuleCat.of B Ω[B⁄A] :=
  ModuleCat.Derivation.desc
    (ModuleCat.Derivation.mk fun b ↦ KaehlerDifferential.D A B b)

/-- `kaehlerOfAlgebraMap` sends the universal derivation to the ambient universal
derivation. -/
theorem kaehlerOfAlgebraMap_d (b : B) :
    kaehlerOfAlgebraMap A B (CommRingCat.KaehlerDifferential.d b) =
      KaehlerDifferential.D A B b := by
  exact ModuleCat.Derivation.desc_d
    (M := ModuleCat.of B Ω[B⁄A]) (f := CommRingCat.ofHom (algebraMap A B))
    (ModuleCat.Derivation.mk (fun b : B ↦ KaehlerDifferential.D A B b)) b

set_option backward.isDefEq.respectTransparency false in
/-- The comparison `kaehlerOfAlgebraMap` is an isomorphism. -/
instance kaehlerOfAlgebraMap_isIso : IsIso (kaehlerOfAlgebraMap A B) := by
  let M := CommRingCat.KaehlerDifferential (CommRingCat.ofHom (algebraMap A B))
  letI : Module B M := M.isModule
  letI := Module.compHom M (algebraMap A B)
  letI : IsScalarTower A B M := IsScalarTower.of_compHom A B M
  let d := CommRingCat.KaehlerDifferential.D (CommRingCat.ofHom (algebraMap A B))
  let D : Derivation A B M :=
    { toFun := d.d
      map_add' := d.d_add
      map_smul' := fun a b ↦ by
        rw [Algebra.smul_def]
        change d.d (algebraMap A B a * b) = algebraMap A B a • d.d b
        have ha : d.d (algebraMap A B a) = 0 := d.d_map a
        rw [d.d_mul, ha, smul_zero, add_zero]
      map_one_eq_zero' := by simpa using d.d_map 1
      leibniz' := d.d_mul }
  let g : ModuleCat.of B Ω[B⁄A] ⟶ M := ModuleCat.ofHom D.liftKaehlerDifferential
  refine ⟨⟨g, ?_, ?_⟩⟩
  · apply CommRingCat.KaehlerDifferential.ext
    intro b
    change D.liftKaehlerDifferential
      (kaehlerOfAlgebraMap A B (CommRingCat.KaehlerDifferential.d b)) = d.d b
    rw [kaehlerOfAlgebraMap_d, D.liftKaehlerDifferential_comp_D]
    rfl
  · apply ModuleCat.hom_ext
    apply Derivation.liftKaehlerDifferential_unique
    ext b
    change kaehlerOfAlgebraMap A B
      (D.liftKaehlerDifferential (KaehlerDifferential.D A B b)) =
        KaehlerDifferential.D A B b
    rw [D.liftKaehlerDifferential_comp_D]
    exact kaehlerOfAlgebraMap_d A B b

/-- The degree-zero component of the canonical cochain comparison `L_{B/A} ⟶ Ω[B⁄A][0]`,
obtained by transporting Kähler base change of the standard-resolution augmentation along
`objXIso` and the comparison `kaehlerOfAlgebraMap`. -/
def toKaehler :
    (Algebra.cotangentComplex A B).X 0 ⟶ ModuleCat.of B Ω[B⁄A] :=
  (objXIso (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))) 0).hom ≫
    standardToKaehler (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))) ≫
      kaehlerOfAlgebraMap A B

set_option backward.isDefEq.respectTransparency false in
/-- The incoming differential of `L_{B/A}` into degree zero followed by `toKaehler` is zero. -/
theorem d_comp_toKaehler (i : ℤ) (h : (ComplexShape.up ℤ).Rel i 0) :
    (Algebra.cotangentComplex A B).d i 0 ≫ toKaehler A B = 0 := by
  have hi : i = -1 := eq_neg_of_add_eq_zero_left h
  subst i
  let R := CommRingCat.of A
  let S := Under.mk (CommRingCat.ofHom (algebraMap A B))
  let K := (alternatingFaceMapComplex (ModuleCat.{u} S.right)).obj (simplicialModule R S)
  change (K.extend ComplexShape.embeddingDownNat).d (-1) 0 ≫
    (K.extendXIso ComplexShape.embeddingDownNat (i := 0) (i' := 0) rfl).hom ≫
      standardToKaehler R S ≫ kaehlerOfAlgebraMap A B = 0
  rw [HomologicalComplex.extend_d_eq K ComplexShape.embeddingDownNat
    (i' := -1) (j' := 0) (i := 1) (j := 0) rfl rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change (K.extendXIso ComplexShape.embeddingDownNat rfl).hom ≫
    (K.d 1 0 ≫ standardToKaehler R S) ≫ kaehlerOfAlgebraMap A B = 0
  have hd : K.d 1 0 ≫ standardToKaehler R S = 0 := by
    dsimp only [K]
    rw [alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD, Fin.sum_univ_two]
    simp only [Fin.val_zero,
      Fin.val_one, pow_zero, pow_one, one_zsmul, neg_smul, Preadditive.add_comp,
      Preadditive.neg_comp]
    change (simplicialModuleMap R S (SimplexCategory.δ (0 : Fin 2)).op ≫
      standardToKaehler R S) +
        -(simplicialModuleMap R S (SimplexCategory.δ (1 : Fin 2)).op ≫
          standardToKaehler R S) = 0
    simpa only [sub_eq_add_neg] using
      sub_eq_zero.mpr (faces_comp_standardToKaehler R S
        (SimplexCategory.δ (0 : Fin 2)).op (SimplexCategory.δ (1 : Fin 2)).op)
  rw [hd, CategoryTheory.Limits.zero_comp, CategoryTheory.Limits.comp_zero]

/-- The canonical cochain comparison `L_{B/A} ⟶ Ω[B⁄A][0]`. -/
def augmentation :
    Algebra.cotangentComplex A B ⟶
      (single (ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj (ModuleCat.of B Ω[B⁄A]) :=
  mkHomToSingle (toKaehler A B) (d_comp_toKaehler A B)

/-- The degree-zero component of `augmentation` is `toKaehler` followed by the inverse of
`singleObjXSelf`. -/
theorem augmentation_f_zero :
    (augmentation A B).f 0 =
      toKaehler A B ≫ (singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of B Ω[B⁄A])).inv := by
  exact mkHomToSingle_f _ _

/-- The canonical map `H^0(L_{B/A}) ⟶ Ω[B⁄A]` induced by `augmentation`. -/
def homologyZeroMap :
    (Algebra.cotangentComplex A B).homology 0 ⟶ ModuleCat.of B Ω[B⁄A] :=
  homologyMap (augmentation A B) 0 ≫
    (singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (ModuleCat.of B Ω[B⁄A])).hom

/-- Every degree-zero element of the cotangent complex determines a homology class,
since the complex vanishes in positive degrees. -/
def toHomologyZero :
    (Algebra.cotangentComplex A B).X 0 ⟶ (Algebra.cotangentComplex A B).homology 0 :=
  (Algebra.cotangentComplex A B).liftCycles (𝟙 _) 1 (by simp)
    (by
      apply (isZero_obj_X_of_pos (CommRingCat.of A)
        (Under.mk (CommRingCat.ofHom (algebraMap A B))) (n := 1) (by decide)).eq_of_tgt) ≫
    (Algebra.cotangentComplex A B).homologyπ 0

set_option backward.isDefEq.respectTransparency false in
private theorem toHomologyZero_comp_map :
    toHomologyZero A B ≫ homologyZeroMap A B = toKaehler A B := by
  dsimp only [toHomologyZero, homologyZeroMap]
  rw [Category.assoc, homologyπ_naturality_assoc, ← Category.assoc,
    liftCycles_comp_cyclesMap, homologyπ_singleObjHomologySelfIso_hom]
  rw [singleObjCyclesSelfIso_hom, ← Category.assoc, liftCycles_i,
    augmentation_f_zero]
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem d_comp_toHomologyZero :
    (Algebra.cotangentComplex A B).d (-1) 0 ≫ toHomologyZero A B = 0 := by
  dsimp only [toHomologyZero]
  rw [← Category.assoc, comp_liftCycles]
  exact (Algebra.cotangentComplex A B).liftCycles_homologyπ_eq_zero_of_boundary
    _ 1 (by simp) (𝟙 _) (by simp)

set_option backward.isDefEq.respectTransparency false in
private theorem faces_comp_toHomologyZero :
    let R := CommRingCat.of A
    let S := Under.mk (CommRingCat.ofHom (algebraMap A B))
    (simplicialModule R S).δ 0 ≫ (objXIso R S 0).inv ≫ toHomologyZero A B =
      (simplicialModule R S).δ 1 ≫ (objXIso R S 0).inv ≫ toHomologyZero A B := by
  dsimp only
  let R := CommRingCat.of A
  let S := Under.mk (CommRingCat.ofHom (algebraMap A B))
  let K := (alternatingFaceMapComplex (ModuleCat.{u} S.right)).obj (simplicialModule R S)
  have hz := d_comp_toHomologyZero A B
  change (K.extend ComplexShape.embeddingDownNat).d (-1) 0 ≫ toHomologyZero A B = 0 at hz
  rw [HomologicalComplex.extend_d_eq K ComplexShape.embeddingDownNat
    (i' := -1) (j' := 0) (i := 1) (j := 0) rfl rfl] at hz
  have hz' : K.d 1 0 ≫ (objXIso R S 0).inv ≫ toHomologyZero A B = 0 := by
    apply (cancel_epi (objXIso R S 1).hom).mp
    simpa only [objXIso, Category.assoc, CategoryTheory.Limits.comp_zero] using hz
  dsimp only [K] at hz'
  rw [alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD, Fin.sum_univ_two] at hz'
  simpa only [Fin.val_zero,
    Fin.val_one, pow_zero, pow_one, one_zsmul, neg_smul, Preadditive.add_comp,
    Preadditive.neg_comp, Preadditive.sub_comp, Category.assoc,
    ← sub_eq_add_neg, sub_eq_zero] using hz'

set_option backward.isDefEq.respectTransparency false in
private theorem toHomologyZero_epi : Epi (toHomologyZero A B) := by
  let K := Algebra.cotangentComplex A B
  let l : K.X 0 ⟶ K.cycles 0 := K.liftCycles (𝟙 _) 1 (by simp)
    (by
      apply (isZero_obj_X_of_pos (CommRingCat.of A)
        (Under.mk (CommRingCat.ofHom (algebraMap A B))) (n := 1) (by decide)).eq_of_tgt)
  have hi : K.iCycles 0 ≫ l = 𝟙 _ := by
    apply (cancel_mono (K.iCycles 0)).mp
    simp only [l, Category.assoc, liftCycles_i, Category.comp_id, Category.id_comp]
  apply epi_of_epi_fac (f := K.iCycles 0) (h := K.homologyπ 0)
  change K.iCycles 0 ≫ l ≫ K.homologyπ 0 = K.homologyπ 0
  rw [← Category.assoc, hi, Category.id_comp]

/-- The homology class of the differential of the universal free-algebra generator indexed
by an element of the algebra, after extension of scalars to the algebra. -/
def homologyZeroGenerator (b : B) : (Algebra.cotangentComplex A B).homology 0 :=
  let R := CommRingCat.of A
  let S := Under.mk (CommRingCat.ofHom (algebraMap A B))
  let x := (eqToHom (CommRingCat.Under.PolynomialResolution.evaluation.obj_eq R S 0).symm).right
    (CommRingCat.Under.FreeAlgebra.generator R b)
  let dx : CommRingCat.KaehlerDifferential (standardTerm R S (op ⦋0⦌)).hom :=
    CommRingCat.KaehlerDifferential.d x
  let dxB := ((ModuleCat.extendRestrictScalarsAdj
    (standardAugmentation R S (op ⦋0⦌)).hom).unit.app
      (CommRingCat.KaehlerDifferential (standardTerm R S (op ⦋0⦌)).hom)) dx
  toHomologyZero A B ((objXIso R S 0).inv dxB)

-- Checking the transported degree-one face maps unfolds the iterated comonad resolution.
set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
private theorem homologyZeroGenerator_eval
    (p : (standardTerm (CommRingCat.of A)
      (Under.mk (CommRingCat.ofHom (algebraMap A B))) (op ⦋0⦌)).right) :
    let R := CommRingCat.of A
    let S := Under.mk (CommRingCat.ofHom (algebraMap A B))
    homologyZeroGenerator A B (standardAugmentation R S (op ⦋0⦌) p) =
      toHomologyZero A B ((objXIso R S 0).inv
        (((ModuleCat.extendRestrictScalarsAdj (standardAugmentation R S (op ⦋0⦌)).hom).unit.app
          (CommRingCat.KaehlerDifferential (standardTerm R S (op ⦋0⦌)).hom))
            (CommRingCat.KaehlerDifferential.d p))) := by
  dsimp only
  let R := CommRingCat.of A
  let S := Under.mk (CommRingCat.ofHom (algebraMap A B))
  let x := (eqToHom (CommRingCat.Under.PolynomialResolution.evaluation.obj_eq R S 1).symm).right
    (CommRingCat.Under.FreeAlgebra.generator R p)
  let dx : CommRingCat.KaehlerDifferential (standardTerm R S (op ⦋1⦌)).hom :=
    CommRingCat.KaehlerDifferential.d x
  let dxB := ((ModuleCat.extendRestrictScalarsAdj
    (standardAugmentation R S (op ⦋1⦌)).hom).unit.app
      (CommRingCat.KaehlerDifferential (standardTerm R S (op ⦋1⦌)).hom)) dx
  -- The two faces identify the differential of `[ε(p)]` with the differential of `p`.
  have h := congrArg (fun f ↦ f dxB) (faces_comp_toHomologyZero A B)
  change toHomologyZero A B ((objXIso R S 0).inv
    (simplicialModuleMap R S (SimplexCategory.δ (0 : Fin 2)).op dxB)) =
      toHomologyZero A B ((objXIso R S 0).inv
        (simplicialModuleMap R S (SimplexCategory.δ (1 : Fin 2)).op dxB)) at h
  dsimp only [dxB, dx, x] at h
  rw [simplicialModuleMap_unit_d, face_zero_generator,
    simplicialModuleMap_unit_d, face_one_generator] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The augmentation comparison sends the homology class of a generator differential to its differential. -/
theorem homologyZeroMap_generator (b : B) :
    homologyZeroMap A B (homologyZeroGenerator A B b) = KaehlerDifferential.D A B b := by
  let R := CommRingCat.of A
  let S := Under.mk (CommRingCat.ofHom (algebraMap A B))
  let x := (eqToHom (CommRingCat.Under.PolynomialResolution.evaluation.obj_eq R S 0).symm).right
    (CommRingCat.Under.FreeAlgebra.generator R b)
  let dx : CommRingCat.KaehlerDifferential (standardTerm R S (op ⦋0⦌)).hom :=
    CommRingCat.KaehlerDifferential.d x
  let dxB := ((ModuleCat.extendRestrictScalarsAdj
    (standardAugmentation R S (op ⦋0⦌)).hom).unit.app
      (CommRingCat.KaehlerDifferential (standardTerm R S (op ⦋0⦌)).hom)) dx
  change (toHomologyZero A B ≫ homologyZeroMap A B) ((objXIso R S 0).inv dxB) = _
  rw [toHomologyZero_comp_map]
  change ((objXIso R S 0).inv ≫ toKaehler A B) dxB = _
  rw [toKaehler, Iso.inv_hom_id_assoc]
  change kaehlerOfAlgebraMap A B (standardToKaehler R S dxB) = _
  exact (congrArg (kaehlerOfAlgebraMap A B) (standardToKaehler_unit_d R S x)).trans
    ((kaehlerOfAlgebraMap_d A B _).trans
      (congrArg (KaehlerDifferential.D A B) (generator_augmentation R S b)))

set_option backward.isDefEq.respectTransparency false in
/-- The homology classes of universal-generator differentials are additive. -/
theorem homologyZeroGenerator_add (b c : B) :
    homologyZeroGenerator A B (b + c) =
      homologyZeroGenerator A B b + homologyZeroGenerator A B c := by
  let R := CommRingCat.of A
  let S := Under.mk (CommRingCat.ofHom (algebraMap A B))
  let gen (b : B) := (eqToHom
    (CommRingCat.Under.PolynomialResolution.evaluation.obj_eq R S 0).symm).right
      (CommRingCat.Under.FreeAlgebra.generator R b)
  have h := homologyZeroGenerator_eval A B (gen b + gen c)
  dsimp only at h
  rw [map_add, generator_augmentation, generator_augmentation] at h
  rw [h]
  simp only [ModuleCat.Derivation.d_add, map_add]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The homology classes of universal-generator differentials satisfy the Leibniz identity. -/
theorem homologyZeroGenerator_mul (b c : B) :
    homologyZeroGenerator A B (b * c) =
      b • homologyZeroGenerator A B c + c • homologyZeroGenerator A B b := by
  let R := CommRingCat.of A
  let S := Under.mk (CommRingCat.ofHom (algebraMap A B))
  let gen (b : B) := (eqToHom
    (CommRingCat.Under.PolynomialResolution.evaluation.obj_eq R S 0).symm).right
      (CommRingCat.Under.FreeAlgebra.generator R b)
  let unit : CommRingCat.KaehlerDifferential (standardTerm R S (op ⦋0⦌)).hom ⟶
      (ModuleCat.restrictScalars (standardAugmentation R S (op ⦋0⦌)).hom).obj
        ((simplicialModule R S).obj (op ⦋0⦌)) :=
    (ModuleCat.extendRestrictScalarsAdj
    (standardAugmentation R S (op ⦋0⦌)).hom).unit.app
      (CommRingCat.KaehlerDifferential (standardTerm R S (op ⦋0⦌)).hom)
  have hunit (r : (standardTerm R S (op ⦋0⦌)).right)
      (m : CommRingCat.KaehlerDifferential (standardTerm R S (op ⦋0⦌)).hom) :
      (unit (r • m) : (simplicialModule R S).obj (op ⦋0⦌)) =
        standardAugmentation R S (op ⦋0⦌) r •
          (unit m : (simplicialModule R S).obj (op ⦋0⦌)) :=
    unit.hom.map_smul r m
  have h := homologyZeroGenerator_eval A B (gen b * gen c)
  dsimp only at h
  rw [map_mul, generator_augmentation, generator_augmentation] at h
  rw [h]
  change toHomologyZero A B ((objXIso R S 0).inv
    (unit (CommRingCat.KaehlerDifferential.d (gen b * gen c)))) = _
  simp only [ModuleCat.Derivation.d_mul, map_add, hunit, map_smul]
  rw [generator_augmentation, generator_augmentation]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The homology class of a universal-generator differential vanishes on the base ring. -/
theorem homologyZeroGenerator_algebraMap (a : A) :
    homologyZeroGenerator A B (algebraMap A B a) = 0 := by
  let R := CommRingCat.of A
  let S := Under.mk (CommRingCat.ofHom (algebraMap A B))
  have ha : standardAugmentation R S (op ⦋0⦌)
      ((standardTerm R S (op ⦋0⦌)).hom a) = algebraMap A B a :=
    congrArg (fun f ↦ f a) ((((CommRingCat.Under.PolynomialResolution.evaluation R).obj S).hom.app
      (op ⦋0⦌)).w)
  have h := homologyZeroGenerator_eval A B ((standardTerm R S (op ⦋0⦌)).hom a)
  dsimp only at h
  rw [ha] at h
  rw [h]
  have hd := (CommRingCat.KaehlerDifferential.D (standardTerm R S (op ⦋0⦌)).hom).d_map a
  let unit : CommRingCat.KaehlerDifferential (standardTerm R S (op ⦋0⦌)).hom ⟶
      (ModuleCat.restrictScalars (standardAugmentation R S (op ⦋0⦌)).hom).obj
        ((simplicialModule R S).obj (op ⦋0⦌)) :=
    (ModuleCat.extendRestrictScalarsAdj
      (standardAugmentation R S (op ⦋0⦌)).hom).unit.app
        (CommRingCat.KaehlerDifferential (standardTerm R S (op ⦋0⦌)).hom)
  exact (congrArg (fun m : CommRingCat.KaehlerDifferential
    (standardTerm R S (op ⦋0⦌)).hom ↦
      toHomologyZero A B ((objXIso R S 0).inv (unit m))) hd).trans
    (by
      change ((objXIso R S 0).inv ≫ toHomologyZero A B) (unit 0) = 0
      have hu : (unit 0 : (simplicialModule R S).obj (op ⦋0⦌)) = 0 := unit.hom.map_zero
      exact (congrArg ((objXIso R S 0).inv ≫ toHomologyZero A B) hu).trans
        ((objXIso R S 0).inv ≫ toHomologyZero A B).hom.map_zero)

section

open scoped ModuleCat.Algebra

/-- The derivation sending an algebra element to the homology class of the differential of
its universal free-algebra generator. -/
def homologyZeroDerivation : Derivation A B ((Algebra.cotangentComplex A B).homology 0) where
  toFun := homologyZeroGenerator A B
  map_add' := homologyZeroGenerator_add A B
  map_smul' a b := by
    rw [Algebra.smul_def, homologyZeroGenerator_mul,
      homologyZeroGenerator_algebraMap, smul_zero, add_zero]
    rfl
  map_one_eq_zero' := by
    change homologyZeroGenerator A B 1 = 0
    simpa only [map_one] using homologyZeroGenerator_algebraMap A B 1
  leibniz' := homologyZeroGenerator_mul A B

/-- The morphism from Kähler differentials to zeroth cotangent-complex homology induced by
the homology classes of universal-generator differentials. -/
def homologyZeroInv :
    ModuleCat.of B Ω[B⁄A] ⟶ (Algebra.cotangentComplex A B).homology 0 :=
  ModuleCat.ofHom (homologyZeroDerivation A B).liftKaehlerDifferential


set_option backward.isDefEq.respectTransparency false in
/-- The inverse comparison sends a universal differential to its generator homology class. -/
theorem homologyZeroInv_d (b : B) :
    homologyZeroInv A B (KaehlerDifferential.D A B b) = homologyZeroGenerator A B b := by
  exact (homologyZeroDerivation A B).liftKaehlerDifferential_comp_D b

end

set_option backward.isDefEq.respectTransparency false in
/-- The canonical differential comparison followed by the universal-generator inverse is
the identity on zeroth cotangent-complex homology. -/
theorem homologyZeroMap_comp_inv :
    homologyZeroMap A B ≫ homologyZeroInv A B = 𝟙 _ := by
  let R := CommRingCat.of A
  let S := Under.mk (CommRingCat.ofHom (algebraMap A B))
  haveI := toHomologyZero_epi A B
  apply (cancel_epi (toHomologyZero A B)).mp
  rw [← Category.assoc, toHomologyZero_comp_map, Category.comp_id]
  apply (cancel_epi (objXIso R S 0).inv).mp
  change (objXIso R S 0).inv ≫ (objXIso R S 0).hom ≫
    standardToKaehler R S ≫ kaehlerOfAlgebraMap A B ≫ homologyZeroInv A B =
      (objXIso R S 0).inv ≫ toHomologyZero A B
  rw [Iso.inv_hom_id_assoc]
  apply ((ModuleCat.extendRestrictScalarsAdj
    (standardAugmentation R S (op ⦋0⦌)).hom).homEquiv _ _).injective
  apply CommRingCat.KaehlerDifferential.ext
  intro p
  change homologyZeroInv A B (kaehlerOfAlgebraMap A B
    (standardToKaehler R S
      (((ModuleCat.extendRestrictScalarsAdj (standardAugmentation R S (op ⦋0⦌)).hom).unit.app
        (CommRingCat.KaehlerDifferential (standardTerm R S (op ⦋0⦌)).hom))
          (CommRingCat.KaehlerDifferential.d p)))) =
    toHomologyZero A B ((objXIso R S 0).inv
      (((ModuleCat.extendRestrictScalarsAdj (standardAugmentation R S (op ⦋0⦌)).hom).unit.app
        (CommRingCat.KaehlerDifferential (standardTerm R S (op ⦋0⦌)).hom))
          (CommRingCat.KaehlerDifferential.d p)))
  rw [standardToKaehler_unit_d, kaehlerOfAlgebraMap_d, homologyZeroInv_d]
  exact homologyZeroGenerator_eval A B p

set_option backward.isDefEq.respectTransparency false in
/-- The universal-generator inverse followed by the canonical differential comparison is
the identity on Kähler differentials. -/
theorem homologyZeroInv_comp_map :
    homologyZeroInv A B ≫ homologyZeroMap A B = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply Derivation.liftKaehlerDifferential_unique
  ext b
  change homologyZeroMap A B (homologyZeroInv A B (KaehlerDifferential.D A B b)) = _
  rw [homologyZeroInv_d]
  exact homologyZeroMap_generator A B b

/-- The canonical comparison from zeroth cotangent-complex homology to Kähler differentials
is an isomorphism. -/
instance homologyZeroMap_isIso : IsIso (homologyZeroMap A B) :=
  ⟨⟨homologyZeroInv A B, homologyZeroMap_comp_inv A B, homologyZeroInv_comp_map A B⟩⟩

/-- Zeroth cohomology of the standard-resolution cotangent complex is canonically
isomorphic to the module of Kähler differentials. -/
def homologyZeroIso :
    (Algebra.cotangentComplex A B).homology 0 ≅ ModuleCat.of B Ω[B⁄A] where
  hom := homologyZeroMap A B
  inv := homologyZeroInv A B
  hom_inv_id := homologyZeroMap_comp_inv A B
  inv_hom_id := homologyZeroInv_comp_map A B

/-- The forward morphism of the zeroth-homology isomorphism is the augmentation comparison. -/
theorem homologyZeroIso_hom :
    (homologyZeroIso A B).hom = homologyZeroMap A B :=
  rfl

/-- The inverse morphism of the zeroth-homology isomorphism is the categorical inverse of
the augmentation comparison. -/
theorem homologyZeroIso_inv :
    (homologyZeroIso A B).inv = inv (homologyZeroMap A B) := by
  exact IsIso.eq_inv_of_hom_inv_id (homologyZeroMap_comp_inv A B)

end Algebra.CotangentComplex
