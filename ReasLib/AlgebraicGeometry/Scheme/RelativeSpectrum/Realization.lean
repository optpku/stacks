module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Gluing.Basis.Basic
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Sections

/-!
# Realizations of relative spectra

This module specializes basis-indexed scheme gluing to the spectra of section
rings of a quasi-coherent algebra sheaf.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

/-- The basis-indexed gluing datum whose local scheme over an affine open `U` is the spectrum
of the section ring of `A` on `U`. -/
def relativeSpectrumGluingData (A : S.QcAlgebraUnder) : BasisSchemeGluing S where
  ι := S.affineOpens
  U U := U
  isBasis := by
    rw [Subtype.range_coe]
    exact S.isBasis_affineOpens
  X U := Spec (qcAlgebraSectionRing A U)
  f U := Spec.map (qcAlgebraStructureMap A U) ≫ U.2.isoSpec.inv
  rho {U U'} h := Spec.map (qcAlgebraSectionRestrict A h)
  isPullback_rho {U U'} h :=
    isPullback_specMap_qcAlgebraSectionRestrict A U.2 U'.2 h
  cocycle {U U' U''} h h' :=
    (specMap_qcAlgebraSectionRestrict_comp A U.2 U'.2 U''.2 h h').symm

/-- A morphism realizes the relative spectrum of `A` when its restrictions to all affine opens
are compatibly identified with the spectra of the corresponding section rings. -/
def realizesRelativeSpectrum (A : S.QcAlgebraUnder) {X : Scheme.{u}} (π : X ⟶ S) : Prop :=
  (relativeSpectrumGluingData A).Realizes π

/-- An equipped relative-spectrum realization consists of a scheme over the base together with
compatible affine-local identifications with spectra of section rings. -/
abbrev RelativeSpectrumRealization (A : S.QcAlgebraUnder) :=
  (relativeSpectrumGluingData A).Realization

/-- An isomorphism of equipped relative-spectrum realizations preserves the structure morphisms
and the chosen affine-local identifications. -/
abbrev RelativeSpectrumRealizationIso (A : S.QcAlgebraUnder)
    (R R' : RelativeSpectrumRealization A) :=
  (relativeSpectrumGluingData A).RealizationIso R R'

namespace RelativeSpectrumRealization

/-- Forgetting the chosen local identifications gives the underlying relative-spectrum
realization property. -/
def realizes {A : S.QcAlgebraUnder} (R : RelativeSpectrumRealization A) :
    realizesRelativeSpectrum A R.toBase :=
  BasisSchemeGluing.Realization.realizes (relativeSpectrumGluingData A) R

/-- Every quasi-coherent algebra sheaf admits an equipped relative-spectrum realization. -/
theorem nonempty (A : S.QcAlgebraUnder) : Nonempty (RelativeSpectrumRealization A) := sorry

/-- Between two equipped relative-spectrum realizations there is a unique compatible
isomorphism. -/
theorem existsUniqueIso (A : S.QcAlgebraUnder) (R R' : RelativeSpectrumRealization A) :
    ∃ e : RelativeSpectrumRealizationIso A R R',
      ∀ e' : RelativeSpectrumRealizationIso A R R', e' = e := sorry

end RelativeSpectrumRealization

/-- There is an equipped relative-spectrum realization uniquely compatibly isomorphic to every
other equipped realization. -/
theorem exists_relativeSpectrumRealization_uniqueUpToUniqueIso
    (A : S.QcAlgebraUnder) :
    ∃ R : RelativeSpectrumRealization A,
      ∀ R' : RelativeSpectrumRealization A,
        ∃ e : RelativeSpectrumRealizationIso A R R',
          ∀ e' : RelativeSpectrumRealizationIso A R R', e' = e := sorry

/-- Every quasi-coherent algebra sheaf admits a scheme over the base that realizes its relative
spectrum. -/
theorem exists_scheme_over_realizingRelativeSpectrum
    (A : S.QcAlgebraUnder) :
    ∃ (X : Scheme.{u}) (π : X ⟶ S), realizesRelativeSpectrum A π := sorry

/-- A morphism realizing a relative spectrum is affine. -/
theorem isAffineHom_of_realizesRelativeSpectrum
    (A : S.QcAlgebraUnder) {X : Scheme.{u}} {π : X ⟶ S}
    (hπ : realizesRelativeSpectrum A π) :
    IsAffineHom π := sorry

end AlgebraicGeometry.Scheme
