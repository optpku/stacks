/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.RingTheory.RestrictedPowerSeries.NaiveCotangent.Homotopy
public import ReasLib.RingTheory.RestrictedPowerSeries.Completion
public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent

/-! # Comparison of restricted and ideal-adic naive cotangent complexes -/

@[expose] public section

open Algebra.Extension
open CategoryTheory
open HomotopyCategory
open RestrictedPowerSeries
open TopologicalRing
open TopologicalRing.Ideal

noncomputable section

universe u

namespace Algebra.NaiveCotangent.Restricted

section Comparison

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsAdicRing A]
variable (ι : Type u) (I : Ideal A)

variable {B : Type u} [CommRing B] [Algebra A B]

namespace Presentation

/-- The `I`-adic completed polynomial presentation associated with a restricted
presentation along the canonical restricted-to-adic equivalence. -/
def toAdic (hI : IsIdealOfDefinition I) (P : Presentation A B ι) :
    Algebra.NaiveCotangent.Adic.Presentation A B I ι :=
  Algebra.NaiveCotangent.Adic.Presentation.ofSurjective
    (P.toAlgHom.comp (adicEquiv ι I hI).symm.toAlgHom)
    (P.surjective.comp (adicEquiv ι I hI).symm.surjective)

/-- The structure map of `toAdic` is the restricted structure map composed with
the inverse identification. -/
theorem toAdic_toAlgHom (hI : IsIdealOfDefinition I) (P : Presentation A B ι) :
    (toAdic ι I hI P).toAlgHom = P.toAlgHom.comp (adicEquiv ι I hI).symm.toAlgHom :=
  sorry

/-- Compatibility of `adicEquiv` with the two structure maps to `B`. -/
private theorem toAdicExtensionHom_commutes (hI : IsIdealOfDefinition I)
    (P : Presentation A B ι) :
    (IsScalarTower.toAlgHom A (toAdic ι I hI P).toExtension.Ring B).comp
        (adicEquiv ι I hI).toAlgHom =
      (IsScalarTower.toAlgHom A B B).comp
        (IsScalarTower.toAlgHom A P.toExtension.Ring B) :=
  sorry

/-- The morphism of extensions induced by `adicEquiv`. -/
@[no_expose] def toAdicExtensionHom (hI : IsIdealOfDefinition I) (P : Presentation A B ι) :
    P.toExtension.Hom (toAdic ι I hI P).toExtension :=
  Extension.Hom.ofAlgHom (adicEquiv ι I hI).toAlgHom
    (toAdicExtensionHom_commutes ι I hI P)

/-- Compatibility of `adicEquiv.symm` with the two structure maps to `B`. -/
private theorem ofAdicExtensionHom_commutes (hI : IsIdealOfDefinition I)
    (P : Presentation A B ι) :
    (IsScalarTower.toAlgHom A P.toExtension.Ring B).comp
        (adicEquiv ι I hI).symm.toAlgHom =
      (IsScalarTower.toAlgHom A B B).comp
        (IsScalarTower.toAlgHom A (toAdic ι I hI P).toExtension.Ring B) :=
  sorry

/-- The morphism of extensions induced by `adicEquiv.symm`. -/
@[no_expose] def ofAdicExtensionHom (hI : IsIdealOfDefinition I) (P : Presentation A B ι) :
    (toAdic ι I hI P).toExtension.Hom P.toExtension :=
  Extension.Hom.ofAlgHom (adicEquiv ι I hI).symm.toAlgHom
    (ofAdicExtensionHom_commutes ι I hI P)

/-- Inverse laws for the conormal maps induced by `adicEquiv`. -/
private theorem cotangentIso_toAdic_comp (hI : IsIdealOfDefinition I)
    (P : Presentation A B ι) :
    (Cotangent.map (toAdicExtensionHom ι I hI P)).comp
        (Cotangent.map (ofAdicExtensionHom ι I hI P)) =
      LinearMap.id :=
  sorry

/-- Inverse laws for the conormal maps induced by `adicEquiv.symm`. -/
private theorem cotangentIso_ofAdic_comp (hI : IsIdealOfDefinition I)
    (P : Presentation A B ι) :
    (Cotangent.map (ofAdicExtensionHom ι I hI P)).comp
        (Cotangent.map (toAdicExtensionHom ι I hI P)) =
      LinearMap.id :=
  sorry

/-- The canonical identification of conormal modules along `adicEquiv`. -/
@[no_expose] def cotangentIso_toAdic (hI : IsIdealOfDefinition I) (P : Presentation A B ι) :
    P.toExtension.Cotangent ≃ₗ[B]
      (toAdic ι I hI P).toExtension.Cotangent :=
  LinearEquiv.ofLinear
    (Cotangent.map (toAdicExtensionHom ι I hI P))
    (Cotangent.map (ofAdicExtensionHom ι I hI P))
    (cotangentIso_toAdic_comp ι I hI P)
    (cotangentIso_ofAdic_comp ι I hI P)

end Presentation

variable [Fintype ι]

/-- Higher components of the `I`-adic Jacobian complex of a transported
restricted presentation are the zero object of `ModuleCat`. -/
private def adicComponentSuccIsoUnit (hI : IsIdealOfDefinition I)
    (P : Presentation A B ι) (n : ℕ) :
    (Adic.complex (Presentation.toAdic ι I hI P)).X (n + 2) ≅
      ModuleCat.of B PUnit :=
  ChainComplex.mk'XIso
    (ModuleCat.of B (ι → B))
    (ModuleCat.of B (Presentation.toAdic ι I hI P).toExtension.Cotangent)
    (ModuleCat.ofHom (Adic.jacobian (Presentation.toAdic ι I hI P)))
    (fun {_ _} _ ↦ ⟨ModuleCat.of B PUnit, 0, CategoryTheory.Limits.zero_comp⟩)
    n

/-- Components of the identification of restricted and `I`-adic Jacobian
complexes along `adicEquiv`. -/
private def toAdicIsoComponent (hI : IsIdealOfDefinition I) (P : Presentation A B ι) :
    ∀ n, (complex P).X n ≅ (Adic.complex (Presentation.toAdic ι I hI P)).X n
  | 0 =>
    (componentZeroIso P).trans
      (Adic.componentZeroIso (Presentation.toAdic ι I hI P)).symm
  | 1 =>
    (componentOneIso P).trans (Presentation.cotangentIso_toAdic ι I hI P).toModuleIso
  | n + 2 =>
    (componentSuccIsoUnit P n).trans (adicComponentSuccIsoUnit ι I hI P n).symm

/-- The componentwise identification along `adicEquiv` commutes with
differentials. -/
private theorem toAdicIsoComponent_comm (hI : IsIdealOfDefinition I)
    (P : Presentation A B ι) (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) :
    (toAdicIsoComponent ι I hI P i).hom ≫
        (Adic.complex (Presentation.toAdic ι I hI P)).d i j =
      (complex P).d i j ≫ (toAdicIsoComponent ι I hI P j).hom :=
  sorry

/-- The restricted Jacobian complex is canonically isomorphic to the `I`-adic
Jacobian complex of the transported presentation, via `adicEquiv`. -/
@[no_expose] def complexIso_toAdic (hI : IsIdealOfDefinition I) (P : Presentation A B ι) :
    complex P ≅ Adic.complex (Presentation.toAdic ι I hI P) :=
  HomologicalComplex.Hom.isoOfComponents (toAdicIsoComponent ι I hI P)
    (toAdicIsoComponent_comm ι I hI P)

/-- The degree-zero component of `complexIso_toAdic` is the identity on
`ι → B`. -/
theorem complexIso_toAdic_X_zero (hI : IsIdealOfDefinition I)
    (P : Presentation A B ι) :
    (complexIso_toAdic ι I hI P).hom.f 0 =
      ((componentZeroIso P).trans
        (Adic.componentZeroIso (Presentation.toAdic ι I hI P)).symm).hom :=
  sorry

/-- The degree-one component of `complexIso_toAdic` is the conormal map of
`adicEquiv`. -/
theorem complexIso_toAdic_X_one (hI : IsIdealOfDefinition I)
    (P : Presentation A B ι) :
    (complexIso_toAdic ι I hI P).hom.f 1 =
      ((componentOneIso P).trans
        (Presentation.cotangentIso_toAdic ι I hI P).toModuleIso).hom :=
  sorry

/-- The restricted Jacobian complex is homotopy equivalent to the `I`-adic
Jacobian complex of the transported presentation. -/
theorem complex_homotopyEquiv_toAdic (hI : IsIdealOfDefinition I)
    (P : Presentation A B ι) :
    Nonempty
      (HomotopyEquiv (complex P)
        (Algebra.NaiveCotangent.Adic.complex (Presentation.toAdic ι I hI P))) :=
  sorry

end Comparison

section IndependentOfIdeal

variable {A B : Type u}
variable [CommRing A] [TopologicalSpace A]
variable [CommRing B] [TopologicalSpace B] [Algebra A B]
variable {ι ι' : Type u} [Fintype ι] [Fintype ι']

/-- For an adic topologically finite-type arrow of adic-star rings with
Noetherian source, finite adic presentations along any two ideals of definition
give isomorphic naive cotangent complexes in the homotopy category. -/
theorem independentOfIdeal [IsAdicStarRing A] [IsAdicStarRing B]
    [IsNoetherianRing A]
    (hφ : Continuous (algebraMap A B))
    (h_adic : (algebraMap A B).IsAdicHom)
    (h_tft : (algebraMap A B).TopologicallyOfFiniteType)
    (I I' : Ideal A) (hI : IsIdealOfDefinition I) (hI' : IsIdealOfDefinition I')
    (P_adic : Adic.Presentation A B I ι)
    (Q_adic : Adic.Presentation A B I' ι') :
    Nonempty
      ((quotient (ModuleCat B) (ComplexShape.down ℕ)).obj
          (Adic.naiveCotangent I P_adic) ≅
        (quotient (ModuleCat B) (ComplexShape.down ℕ)).obj
          (Adic.naiveCotangent I' Q_adic)) :=
  sorry

end IndependentOfIdeal

end Algebra.NaiveCotangent.Restricted
