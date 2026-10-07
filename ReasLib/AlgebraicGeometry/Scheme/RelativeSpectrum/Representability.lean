module

public import Mathlib.CategoryTheory.RepresentedBy
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Basic
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Realization

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

/-- A realization of a relative spectrum and a scheme representing its functor of points are
isomorphic over the base. -/
theorem nonempty_iso_over_of_realizesRelativeSpectrum_and_isRepresentedBy
    (A : S.QcAlgebraUnder) {X Y : Scheme.{u}} {πX : X ⟶ S}
    (hX : realizesRelativeSpectrum A πX)
    (x : relativeSpectrumPair A Y)
    (hx : (relativeSpectrumFunctor A).IsRepresentedBy x) :
    Nonempty (Over.mk πX ≅ Over.mk x.1) := sorry

end AlgebraicGeometry.Scheme
