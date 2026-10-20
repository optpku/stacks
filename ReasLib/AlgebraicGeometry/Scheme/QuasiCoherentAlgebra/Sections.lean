module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Basic

/-!
# Sections of quasi-coherent algebra sheaves

This leaf supplies the section-ring and restriction maps used by affine-local
constructions on quasi-coherent algebra sheaves.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

/-- The ring of sections of a quasi-coherent `𝒪_S`-algebra on an open subset of `S`. -/
abbrev qcAlgebraSectionRing (A : S.QcAlgebraUnder) (U : S.Opens) : CommRingCat :=
  A.obj.right.1.obj (op U)

/-- The restriction map on the section rings of a quasi-coherent `𝒪_S`-algebra. -/
abbrev qcAlgebraSectionRestrict (A : S.QcAlgebraUnder) {U U' : S.Opens} (h : U ≤ U') :
    qcAlgebraSectionRing A U' ⟶ qcAlgebraSectionRing A U :=
  A.obj.right.1.map (homOfLE h).op

/-- The structure map from sections of `𝒪_S` to sections of a quasi-coherent algebra. -/
abbrev qcAlgebraStructureMap (A : S.QcAlgebraUnder) (U : S.Opens) :
    S.presheaf.obj (op U) ⟶ qcAlgebraSectionRing A U :=
  (InducedCategory.Hom.hom A.obj.hom).app (op U)

/-- The affine spectra of the section rings over nested affine opens form a pullback square. -/
theorem isPullback_specMap_qcAlgebraSectionRestrict
    (A : S.QcAlgebraUnder) {U U' : S.Opens}
    (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (h : U ≤ U') :
    IsPullback
      (Spec.map (qcAlgebraSectionRestrict A h))
      (Spec.map (qcAlgebraStructureMap A U) ≫ hU.isoSpec.inv)
      (Spec.map (qcAlgebraStructureMap A U') ≫ hU'.isoSpec.inv)
      (S.homOfLE h) := sorry

/-- Affine-spectrum maps induced by successive section restrictions compose as expected. -/
theorem specMap_qcAlgebraSectionRestrict_comp
    (A : S.QcAlgebraUnder) {U U' U'' : S.Opens}
    (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (hU'' : IsAffineOpen U'')
    (h : U ≤ U') (h' : U' ≤ U'') :
    Spec.map (qcAlgebraSectionRestrict A h) ≫
        Spec.map (qcAlgebraSectionRestrict A h') =
      Spec.map (qcAlgebraSectionRestrict A (h.trans h')) := sorry

end AlgebraicGeometry.Scheme
