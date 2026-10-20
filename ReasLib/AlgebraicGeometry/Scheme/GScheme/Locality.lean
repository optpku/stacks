/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GScheme
public import ReasLib.AlgebraicGeometry.Scheme.LocalRingProperty.Locality
public import ReasLib.RingTheory.Regular.GRing.Locality

/-!
# Local criteria for G-schemes

The G-scheme property can be tested on every affine open, on one affine open
cover, or on one open cover. It is preserved by restriction to open subschemes.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme is a G-scheme if and only if the section ring of every affine open
is a G-ring. -/
theorem gScheme_iff_forall_affineOpen (X : Scheme.{u}) :
    GScheme X ↔ ∀ U : X.affineOpens, IsGRing Γ(X, U) :=
  hasRingPropertyLocally_iff_forall_affineOpen_sectionsRing X
    (fun A : CommRingCat.{u} ↦ IsGRing A)

/-- A scheme is a G-scheme if and only if some affine open cover has G-ring
section rings. -/
theorem gScheme_iff_exists_affineOpenCover (X : Scheme.{u}) :
    GScheme X ↔
      ∃ 𝒰 : X.AffineOpenCover, ∀ i : 𝒰.I₀, IsGRing Γ(X, (𝒰.f i).opensRange) :=
  hasRingPropertyLocally_iff_exists_affineOpenCover_sectionsRing X
    (fun A : CommRingCat.{u} ↦ IsGRing A)

/-- A scheme is a G-scheme if and only if some open cover consists of G-scheme
open subschemes. -/
theorem gScheme_iff_exists_openCover (X : Scheme.{u}) :
    GScheme X ↔
      ∃ 𝒰 : X.OpenCover, ∀ i : 𝒰.I₀, GScheme ((𝒰.f i).opensRange).toScheme :=
  hasRingPropertyLocally_iff_exists_openCover_by_hasRingPropertyLocally X
    (fun A : CommRingCat.{u} ↦ IsGRing A)

/-- Every open subscheme of a G-scheme is a G-scheme. -/
theorem gScheme_toScheme {X : Scheme.{u}} [GScheme X] (U : X.Opens) :
    GScheme U.toScheme :=
  hasRingPropertyLocally_toScheme (P := fun A : CommRingCat.{u} ↦ IsGRing A)
    (inferInstance : GScheme X) U

end AlgebraicGeometry.Scheme
