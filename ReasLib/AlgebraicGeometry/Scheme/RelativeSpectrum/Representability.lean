/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.RepresentedBy
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.PointMap

/-!
# Representability of the relative-spectrum functor

This leaf records affine-local and global representability of the
relative-spectrum functor, together with comparison to affine-local
realizations.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

/-- Over an affine base, the relative-spectrum functor is represented by the spectrum of the
global section ring of the algebra sheaf. -/
theorem relativeSpectrumFunctor_isRepresentedBySpecGlobalSections [IsAffine S]
    (A : S.QcAlgebraUnder) :
    ∃ x : (relativeSpectrumFunctor A).obj (op (Spec (qcAlgebraSectionRing A ⊤))),
      (relativeSpectrumFunctor A).IsRepresentedBy x := sorry

/-- The relative-spectrum functor is representable when the base scheme is affine. -/
instance relativeSpectrumFunctor.instIsRepresentableOfIsAffine [IsAffine S]
    (A : S.QcAlgebraUnder) :
    (relativeSpectrumFunctor A).IsRepresentable := sorry

/-- The relative-spectrum functor of a quasi-coherent algebra sheaf is representable. -/
instance relativeSpectrumFunctor.instIsRepresentable (A : S.QcAlgebraUnder) :
    (relativeSpectrumFunctor A).IsRepresentable := sorry

/-- The explicit glued relative-spectrum model represents the relative-spectrum functor via its
universal point. -/
theorem relativeSpectrumFunctor_isRepresentedBy_relativeSpectrumOver (A : S.QcAlgebraUnder) :
    (relativeSpectrumFunctor A).IsRepresentedBy (relativeSpectrumOver A).point := by
  refine ⟨?_⟩
  intro T
  exact (relativeSpectrumHomEquiv A T).bijective

/-- A realization of a relative spectrum and a scheme representing its functor of points are
isomorphic over the base. -/
noncomputable def relativeSpectrumRealizationComparisonIso
    (A : S.QcAlgebraUnder) {X Y : Scheme.{u}} {πX : X ⟶ S}
    (hX : realizesRelativeSpectrum A πX)
    (x : relativeSpectrumPair A Y)
    (hx : (relativeSpectrumFunctor A).IsRepresentedBy x) : X ≅ Y := by
  let D := relativeSpectrumGluingData A
  change D.Realizes πX at hX
  let iScheme := Classical.choose hX
  let hi := Classical.choose_spec hX
  let R : D.Realization :=
    { Y := X
      toBase := πX
      localIso := iScheme
      localIso_hom_over := hi.1
      localTransition := hi.2 }
  let R₀ := relativeSpectrumRealization A
  let e := Classical.choose (BasisSchemeGluing.Realization.existsUniqueIso D R R₀)
  let hR₀ := relativeSpectrumFunctor_isRepresentedBy_relativeSpectrumOver A
  let e₀ := hR₀.representableBy.uniqueUpToIso hx.representableBy
  exact (show R.Y ≅ R₀.Y from e.iso) ≪≫ e₀

noncomputable def nonempty_iso_over_of_realizesRelativeSpectrum_and_isRepresentedBy
    (A : S.QcAlgebraUnder) {X Y : Scheme.{u}} {πX : X ⟶ S}
    (hX : realizesRelativeSpectrum A πX)
    (x : relativeSpectrumPair A Y)
    (hx : (relativeSpectrumFunctor A).IsRepresentedBy x) :
    Over.mk πX ≅ Over.mk x.1 :=
  Over.isoMk (relativeSpectrumRealizationComparisonIso A hX x hx) (by sorry)

@[simp]
theorem nonempty_iso_over_of_realizesRelativeSpectrum_and_isRepresentedBy_hom
    (A : S.QcAlgebraUnder) {X Y : Scheme.{u}} {πX : X ⟶ S}
    (hX : realizesRelativeSpectrum A πX)
    (x : relativeSpectrumPair A Y)
    (hx : (relativeSpectrumFunctor A).IsRepresentedBy x) :
    (nonempty_iso_over_of_realizesRelativeSpectrum_and_isRepresentedBy A hX x hx).hom.left =
      (relativeSpectrumRealizationComparisonIso A hX x hx).hom := rfl

end AlgebraicGeometry.Scheme
