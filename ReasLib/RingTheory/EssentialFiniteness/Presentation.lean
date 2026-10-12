/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Extension.Presentation.Core
public import ReasLib.RingTheory.EssentialFiniteness.Basic

/-!
# Presentation Descent Along Localizations

This module records the coefficient-clearing and descended-presentation API
used to compose essentially finitely presented algebras.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace Algebra

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- A finite subset of a localization is contained in the range of one principal away map. -/
theorem exists_awayMap_range_finset {Q : Type*} [CommRing Q] [Algebra R Q]
    [Algebra Q S] [IsScalarTower R Q S] (M : Submonoid Q) [IsLocalization M S]
    (u : Finset S) :
    ∃ m : M, ∀ x ∈ u,
      x ∈ Set.range
        (Localization.awayLift (algebraMap Q S) (m : Q) (IsLocalization.map_units S m)) := sorry

/-- The away lift from a principal localization to `S` extends the original map from `Q`. -/
theorem isScalarTower_awayLift {Q : Type*} [CommRing Q] [Algebra R Q]
    [Algebra Q S] [IsScalarTower R Q S] {M : Submonoid Q} [IsLocalization M S] (m : M) :
    let A0 := Localization.Away (m : Q)
    letI : Algebra A0 S :=
      (Localization.awayLift (algebraMap Q S) (m : Q) (IsLocalization.map_units S m)).toAlgebra
    IsScalarTower Q A0 S := sorry

omit [Algebra R S] in
/-- On the principal-localization surface, the away-lift algebra map composes to the original
map `Q → S`. -/
theorem awayLift_owner_surface_eq {Q : Type*} [CommRing Q] [Algebra R Q]
    [Algebra Q S] {M : Submonoid Q} [IsLocalization M S] (m : M) :
    let A0 := Localization.Away (m : Q)
    letI : CommRing A0 := inferInstance
    letI : Algebra Q A0 := inferInstance
    letI : Algebra A0 S :=
      (Localization.awayLift (algebraMap Q S) (m : Q) (IsLocalization.map_units S m)).toAlgebra
    (algebraMap A0 S).comp (algebraMap Q A0) = algebraMap Q S := sorry

/-- On the principal-localization surface, the away lift preserves the structural map `R → S`. -/
theorem awayLift_base_surface_eq {Q : Type*} [CommRing Q] [Algebra R Q]
    [Algebra Q S] [IsScalarTower R Q S] {M : Submonoid Q} [IsLocalization M S] (m : M) :
    let A0 := Localization.Away (m : Q)
    letI : CommRing A0 := inferInstance
    letI : Algebra Q A0 := inferInstance
    letI : Algebra A0 S :=
      (Localization.awayLift (algebraMap Q S) (m : Q) (IsLocalization.map_units S m)).toAlgebra
    letI : Algebra R A0 := ((algebraMap Q A0).comp (algebraMap R Q)).toAlgebra
    (algebraMap A0 S).comp (algebraMap R A0) = algebraMap R S := sorry

/-- Composing an away lift with `S → P` preserves the base map `R → P`. -/
theorem awayLift_comp_surface_eq {Q : Type*} [CommRing Q] [Algebra R Q]
    [Algebra Q S] [IsScalarTower R Q S] {P : Type*} [CommRing P] [Algebra R P] [Algebra S P]
    [IsScalarTower R S P] {M : Submonoid Q} [IsLocalization M S] (m : M) :
    let A0 := Localization.Away (m : Q)
    letI : CommRing A0 := inferInstance
    letI : Algebra Q A0 := inferInstance
    letI : Algebra A0 S :=
      (Localization.awayLift (algebraMap Q S) (m : Q) (IsLocalization.map_units S m)).toAlgebra
    letI : Algebra R A0 := ((algebraMap Q A0).comp (algebraMap R Q)).toAlgebra
    letI : Algebra A0 P := ((algebraMap S P).comp (algebraMap A0 S)).toAlgebra
    (algebraMap A0 P).comp (algebraMap R A0) = algebraMap R P := sorry

/-- A finite presentation over a localization has all of its coefficients over one principal
localization of the source. -/
theorem Presentation.exists_away_hasCoeffs {Q : Type*} [CommRing Q] [Algebra R Q]
    [Algebra Q S] [IsScalarTower R Q S] {P : Type*} [CommRing P] [Algebra S P]
    (Ppres : Algebra.Presentation S P ι σ) [Finite ι] [Finite σ] (M : Submonoid Q)
    [IsLocalization M S] :
    ∃ m : M,
      let A0 := Localization.Away (m : Q)
      letI : CommRing A0 := inferInstance
      letI : Algebra Q A0 := inferInstance
      letI : Algebra A0 S :=
        (Localization.awayLift (algebraMap Q S) (m : Q) (IsLocalization.map_units S m)).toAlgebra
      letI : IsScalarTower Q A0 S := isScalarTower_awayLift (R := R) (Q := Q) (S := S) (m := m)
      letI : Algebra A0 P := ((algebraMap S P).comp (algebraMap A0 S)).toAlgebra
      letI : IsScalarTower A0 S P := IsScalarTower.of_algebraMap_eq' rfl
      Ppres.HasCoeffs A0 := sorry

/-- After localizing `Q` away from a member of `M`, `S` is still a localization at the image of
`M`. -/
theorem isLocalization_away_target_of_mem {Q : Type*} [CommRing Q] [Algebra R Q]
    [Algebra Q S] [IsScalarTower R Q S] (M : Submonoid Q) [IsLocalization M S] (m : M) :
    let A0 := Localization.Away (m : Q)
    letI : CommRing A0 := inferInstance
    letI : Algebra Q A0 := inferInstance
    letI : Algebra A0 S :=
      (Localization.awayLift (algebraMap Q S) (m : Q) (IsLocalization.map_units S m)).toAlgebra
    letI : IsScalarTower Q A0 S := isScalarTower_awayLift (R := R) (Q := Q) (S := S) (m := m)
    IsLocalization (Algebra.algebraMapSubmonoid A0 M) S := sorry

/-- The descended model of a presentation with coefficients in `A0` localizes to the target. -/
theorem Presentation.isLocalization_modelOfHasCoeffs {P : Type*} [CommRing P] [Algebra S P]
    (Ppres : Algebra.Presentation S P ι σ) {A0 : Type*} [CommRing A0] [Algebra A0 S] [Algebra A0 P]
    [IsScalarTower A0 S P] [Ppres.HasCoeffs A0] (M0 : Submonoid A0) [IsLocalization M0 S] :
    let P0 := Ppres.ModelOfHasCoeffs A0
    letI : CommRing P0 := inferInstance
    letI : Algebra A0 P0 := inferInstance
    letI : Algebra P0 P :=
      (((Ppres.tensorModelOfHasCoeffsEquiv A0).toRingHom.comp
        Algebra.TensorProduct.includeRight.toRingHom)).toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid P0 M0) P := sorry

/-- The descended model map factors the original coefficient algebra map through the model. -/
theorem Presentation.descended_model_algebraMap_eq {P : Type*} [CommRing P] [Algebra S P]
    (Ppres : Algebra.Presentation S P ι σ) {A0 : Type*} [CommRing A0] [Algebra A0 S] [Algebra A0 P]
    [IsScalarTower A0 S P] [Ppres.HasCoeffs A0] :
    let P0 := Ppres.ModelOfHasCoeffs A0
    letI : CommRing P0 := inferInstance
    letI : Algebra A0 P0 := inferInstance
    letI : Algebra P0 P :=
      (((Ppres.tensorModelOfHasCoeffsEquiv A0).toRingHom.comp
        Algebra.TensorProduct.includeRight.toRingHom)).toAlgebra
    (algebraMap P0 P).comp (algebraMap A0 P0) = algebraMap A0 P := sorry

omit [Algebra R S] in
/-- The descended model of a presentation inherits the expected scalar tower over `R`. -/
theorem Presentation.isScalarTower_modelOfHasCoeffs {P : Type*} [CommRing P] [Algebra R P]
    [Algebra S P] (Ppres : Algebra.Presentation S P ι σ) {A0 : Type*} [CommRing A0]
    [Algebra R A0] [Algebra A0 S] [Algebra A0 P] [IsScalarTower A0 S P]
    [IsScalarTower R A0 P] [Ppres.HasCoeffs A0] :
    let P0 := Ppres.ModelOfHasCoeffs A0
    letI : CommRing P0 := inferInstance
    letI : Algebra A0 P0 := inferInstance
    letI : Algebra R P0 := inferInstance
    letI : Algebra P0 P :=
      (((Ppres.tensorModelOfHasCoeffsEquiv A0).toRingHom.comp
        Algebra.TensorProduct.includeRight.toRingHom)).toAlgebra
    IsScalarTower R P0 P := sorry

/-- The localization of a descended model followed by a localization of its target is a single
localization of the descended model. -/
theorem Presentation.isLocalization_modelOfHasCoeffs_comp {P : Type*} [CommRing P] [Algebra S P]
    (Ppres : Algebra.Presentation S P ι σ) {A0 : Type*} [CommRing A0] [Algebra A0 S] [Algebra A0 P]
    [IsScalarTower A0 S P] [Ppres.HasCoeffs A0] (M0 : Submonoid A0) [IsLocalization M0 S]
    {T : Type*} [CommRing T] [Algebra P T] (N : Submonoid P) [IsLocalization N T] :
    let P0 := Ppres.ModelOfHasCoeffs A0
    letI : CommRing P0 := inferInstance
    letI : Algebra A0 P0 := inferInstance
    letI : Algebra P0 P :=
      (((Ppres.tensorModelOfHasCoeffsEquiv A0).toRingHom.comp
        Algebra.TensorProduct.includeRight.toRingHom)).toAlgebra
    letI : Algebra P0 T := ((algebraMap P T).comp (algebraMap P0 P)).toAlgebra
    IsLocalization
      (IsLocalization.localizationLocalizationSubmodule
        (Algebra.algebraMapSubmonoid P0 M0) N) T := sorry

/-- A descended finite presentation remains finitely presented over its original base ring. -/
theorem Presentation.finitePresentation_modelOfHasCoeffs_base {P : Type*} [CommRing P]
    [Algebra S P] (Ppres : Algebra.Presentation S P ι σ) {A0 : Type*} [CommRing A0]
    [Algebra R A0] [Algebra A0 S] [Algebra A0 P] [IsScalarTower R A0 S] [IsScalarTower A0 S P]
    [Ppres.HasCoeffs A0] [Finite ι] [Finite σ] [Algebra.FinitePresentation R A0] :
    Algebra.FinitePresentation R (Ppres.ModelOfHasCoeffs A0) := sorry

/-- The canonical principal-localization surface makes `R → Localization.Away m → S` a scalar
tower. -/
theorem canonical_away_scalarTower_base {Q : Type*} [CommRing Q] [Algebra R Q]
    [Algebra Q S] [IsScalarTower R Q S] {M : Submonoid Q} [IsLocalization M S] (m : M) :
    letI : Algebra (Localization.Away (m : Q)) S :=
      (Localization.awayLift (algebraMap Q S) (m : Q) (IsLocalization.map_units S m)).toAlgebra
    letI : Algebra R (Localization.Away (m : Q)) := inferInstance
    IsScalarTower R (Localization.Away (m : Q)) S := sorry

/-- Composing the canonical principal-localization surface with `S → P` preserves its scalar
tower over `R`. -/
theorem canonical_away_scalarTower_comp {Q : Type*} [CommRing Q] [Algebra R Q]
    [Algebra Q S] [IsScalarTower R Q S] {P : Type*} [CommRing P] [Algebra R P] [Algebra S P]
    [IsScalarTower R S P] {M : Submonoid Q} [IsLocalization M S] (m : M) :
    letI : Algebra (Localization.Away (m : Q)) S :=
      (Localization.awayLift (algebraMap Q S) (m : Q) (IsLocalization.map_units S m)).toAlgebra
    letI : Algebra R (Localization.Away (m : Q)) := inferInstance
    letI : Algebra (Localization.Away (m : Q)) P :=
      ((algebraMap S P).comp (algebraMap (Localization.Away (m : Q)) S)).toAlgebra
    IsScalarTower R (Localization.Away (m : Q)) P := sorry

/-- A principal localization of a finitely presented algebra is finitely presented over the same
base. -/
theorem canonical_away_finitePresentation_base {Q : Type*} [CommRing Q] [Algebra R Q]
    [Algebra.FinitePresentation R Q] {M : Submonoid Q} (m : M) :
    Algebra.FinitePresentation R (Localization.Away (m : Q)) := sorry

/-- Compose two essential finite-presentation witnesses by descending the second presentation to
a principal localization of the first model. -/
theorem exists_away_descended_model_witness {T : Type w} [CommRing T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] (hRS : EssFinitePresentation R S) (hST : EssFinitePresentation S T) :
    ∃ (P0 : Type u) (_ : CommRing P0) (_ : Algebra R P0) (_ : Algebra P0 T)
      (_ : IsScalarTower R P0 T) (_ : Algebra.FinitePresentation R P0) (N0 : Submonoid P0),
      IsLocalization N0 T := sorry

/-- Composition preserves essential finite presentation. -/
theorem EssFinitePresentation.trans {T : Type w} [CommRing T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] (hRS : EssFinitePresentation R S) (hST : EssFinitePresentation S T) :
    EssFinitePresentation R T := sorry

end Algebra
