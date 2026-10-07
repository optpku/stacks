module

public import stacks_project.Chap110.Lemma_110_43_1_Cotangent
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Degree-zero homology of the André-Quillen cotangent complex

Lemma 92.4.5 identifies `H^0(L_{B/A})` with the module of Kähler differentials `Ω[B⁄A]`
as `B`-modules. The comparison is the degree-zero homology of the cochain augmentation
whose degree-zero component is Kähler base change along the standard-resolution
augmentation `P_0 → B`.
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

/-- The standard-resolution augmentation `P_n → B` is a morphism of objects of `Under A`. -/
theorem standardAugmentation_w (A : CommRingCat.{u}) (B : Under A)
    (n : SimplexCategoryᵒᵖ) :
    𝟙 A ≫ B.hom = (standardTerm A B n).hom ≫ standardAugmentation A B n :=
  sorry

/-- The Kähler base-change map `Ω_{P_0/A} ⊗_{P_0} B ⟶ Ω_{B/A}` along the
standard-resolution augmentation. -/
def standardToKaehler (A : CommRingCat.{u}) (B : Under A) :
    (simplicialModule A B).obj (op ⦋0⦌) ⟶ CommRingCat.KaehlerDifferential B.hom :=
  ((ModuleCat.extendRestrictScalarsAdj
      (standardAugmentation A B (op ⦋0⦌)).hom).homEquiv _ _).symm
    (CommRingCat.KaehlerDifferential.map
      ((Category.id_comp B.hom).trans
        (((PolynomialResolution.evaluation A).obj B).hom.app (op ⦋0⦌)).w.symm))

/-- `standardToKaehler` is the adjunction transpose of Kähler base change along the
standard-resolution augmentation. -/
theorem standardToKaehler_eq (A : CommRingCat.{u}) (B : Under A) :
    standardToKaehler A B =
      ((ModuleCat.extendRestrictScalarsAdj
          (standardAugmentation A B (op ⦋0⦌)).hom).homEquiv _ _).symm
        (CommRingCat.KaehlerDifferential.map
          ((Category.id_comp B.hom).trans
            (((PolynomialResolution.evaluation A).obj B).hom.app (op ⦋0⦌)).w.symm)) :=
  sorry

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
      KaehlerDifferential.D A B b :=
  sorry

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

/-- The outgoing differential of `L_{B/A}` into degree zero followed by `toKaehler` is zero. -/
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
      toKaehler A B ≫ (singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of B Ω[B⁄A])).inv :=
  sorry

/-- The canonical map `H^0(L_{B/A}) ⟶ Ω[B⁄A]` induced by `augmentation`. -/
def homologyZeroMap :
    (Algebra.cotangentComplex A B).homology 0 ⟶ ModuleCat.of B Ω[B⁄A] :=
  homologyMap (augmentation A B) 0 ≫
    (singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (ModuleCat.of B Ω[B⁄A])).hom

/-- The canonical map `H^0(L_{B/A}) ⟶ Ω[B⁄A]` is an isomorphism. -/
instance homologyZeroMap_isIso : IsIso (homologyZeroMap A B) :=
  sorry

/-- Lemma 92.4.5. If `A → B` is a ring map, then `H^0(L_{B/A}) = Ω_{B/A}` as `B`-modules. -/
@[stacks 08QF]
def homologyZeroIso :
    (Algebra.cotangentComplex A B).homology 0 ≅ ModuleCat.of B Ω[B⁄A] :=
  asIso (homologyZeroMap A B)

/-- The forward morphism of `homologyZeroIso` is `homologyZeroMap`. -/
theorem homologyZeroIso_hom :
    (homologyZeroIso A B).hom = homologyZeroMap A B :=
  sorry

/-- The inverse morphism of `homologyZeroIso` is the inverse of `homologyZeroMap`. -/
theorem homologyZeroIso_inv :
    (homologyZeroIso A B).inv = inv (homologyZeroMap A B) :=
  sorry

end Algebra.CotangentComplex

