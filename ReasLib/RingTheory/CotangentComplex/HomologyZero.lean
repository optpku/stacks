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

/-- The comparison `kaehlerOfAlgebraMap` is an isomorphism. -/
instance kaehlerOfAlgebraMap_isIso : IsIso (kaehlerOfAlgebraMap A B) :=
  sorry

/-- The degree-zero component of the canonical cochain comparison `L_{B/A} ⟶ Ω[B⁄A][0]`,
obtained by transporting Kähler base change of the standard-resolution augmentation along
`objXIso` and the comparison `kaehlerOfAlgebraMap`. -/
def toKaehler :
    (Algebra.cotangentComplex A B).X 0 ⟶ ModuleCat.of B Ω[B⁄A] :=
  (objXIso (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))) 0).hom ≫
    standardToKaehler (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))) ≫
      kaehlerOfAlgebraMap A B

/-- The incoming differential of `L_{B/A}` into degree zero followed by `toKaehler` is zero. -/
theorem d_comp_toKaehler (i : ℤ) (h : (ComplexShape.up ℤ).Rel i 0) :
    (Algebra.cotangentComplex A B).d i 0 ≫ toKaehler A B = 0 :=
  sorry

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

/-- The homology classes of universal-generator differentials are additive. -/
theorem homologyZeroGenerator_add (b c : B) :
    homologyZeroGenerator A B (b + c) =
      homologyZeroGenerator A B b + homologyZeroGenerator A B c :=
  sorry

/-- The homology classes of universal-generator differentials satisfy the Leibniz identity. -/
theorem homologyZeroGenerator_mul (b c : B) :
    homologyZeroGenerator A B (b * c) =
      b • homologyZeroGenerator A B c + c • homologyZeroGenerator A B b :=
  sorry

/-- The homology class of a universal-generator differential vanishes on the base ring. -/
theorem homologyZeroGenerator_algebraMap (a : A) :
    homologyZeroGenerator A B (algebraMap A B a) = 0 :=
  sorry

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

end

/-- The canonical differential comparison followed by the universal-generator inverse is
the identity on zeroth cotangent-complex homology. -/
theorem homologyZeroMap_comp_inv :
    homologyZeroMap A B ≫ homologyZeroInv A B = 𝟙 _ :=
  sorry

/-- The universal-generator inverse followed by the canonical differential comparison is
the identity on Kähler differentials. -/
theorem homologyZeroInv_comp_map :
    homologyZeroInv A B ≫ homologyZeroMap A B = 𝟙 _ :=
  sorry

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
