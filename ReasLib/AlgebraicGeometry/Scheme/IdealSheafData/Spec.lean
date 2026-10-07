module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-!
# Ideal sheaves on affine spectra

This file records the ideal-sheaf datum on an affine spectrum associated to an ideal of its
coordinate ring.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The ideal-sheaf datum on `Spec A` associated to an ideal of `A`, transported across the
canonical isomorphism between `A` and the global sections of `Spec A`. -/
abbrev idealSheafDataOfIdealOnSpec {A : Type u} [CommRing A] (I : Ideal A) :
    (Spec (CommRingCat.of A)).IdealSheafData :=
  IdealSheafData.ofIdealTop
    (I.comap (CommRingCat.Hom.hom (ΓSpecIso (CommRingCat.of A)).hom))

end AlgebraicGeometry.Scheme
