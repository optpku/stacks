/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Seminormal
import StacksCheckRecall

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

variable (X : Scheme.{u})

/- Lemma 29.47.4 (1): a scheme is seminormal exactly when the section ring of
every affine open is seminormal. -/
@[stacks 0EUP]
#check (AlgebraicGeometry.Scheme.hasRingPropertyLocally_iff_forall_affineOpen_sectionsRing X
    (fun A : CommRingCat.{u} ↦ SeminormalRing A) :
  AlgebraicGeometry.Scheme.Seminormal X ↔
    ∀ U : X.affineOpens, SeminormalRing (Γ(X, U)))

/- Lemma 29.47.4 (2): a scheme is seminormal exactly when some affine open cover
has seminormal section rings. -/
@[stacks 0EUP]
#check (AlgebraicGeometry.Scheme.hasRingPropertyLocally_iff_exists_affineOpenCover_sectionsRing X
    (fun A : CommRingCat.{u} ↦ SeminormalRing A) :
  AlgebraicGeometry.Scheme.Seminormal X ↔
    ∃ 𝒰 : X.AffineOpenCover,
      ∀ i : 𝒰.I₀, SeminormalRing (Γ(X, (𝒰.f i).opensRange)))

/- Lemma 29.47.4 (3): a scheme is seminormal exactly when some open cover
consists of seminormal open subschemes. -/
@[stacks 0EUP]
#check (AlgebraicGeometry.Scheme.hasRingPropertyLocally_iff_exists_openCover_by_hasRingPropertyLocally X
    (fun A : CommRingCat.{u} ↦ SeminormalRing A) :
  AlgebraicGeometry.Scheme.Seminormal X ↔
    ∃ 𝒰 : X.OpenCover,
      ∀ i : 𝒰.I₀, AlgebraicGeometry.Scheme.Seminormal ((𝒰.f i).opensRange).toScheme)

/- Lemma 29.47.4 (4): seminormality restricts to every open subscheme. -/
@[stacks 0EUP]
#check (AlgebraicGeometry.Scheme.hasRingPropertyLocally_toScheme
    (X := X) (P := fun A : CommRingCat.{u} ↦ SeminormalRing A) :
  AlgebraicGeometry.Scheme.Seminormal X →
    ∀ U : X.Opens, AlgebraicGeometry.Scheme.Seminormal U.toScheme)

/- Lemma 29.47.4 (5): a scheme is absolutely weakly normal exactly when the
section ring of every affine open is absolutely weakly normal. -/
@[stacks 0EUP]
#check (AlgebraicGeometry.Scheme.hasRingPropertyLocally_iff_forall_affineOpen_sectionsRing X
    (fun A : CommRingCat.{u} ↦ AbsolutelyWeaklyNormalRing A) :
  AlgebraicGeometry.Scheme.AbsolutelyWeaklyNormal X ↔
    ∀ U : X.affineOpens, AbsolutelyWeaklyNormalRing (Γ(X, U)))

/- Lemma 29.47.4 (6): a scheme is absolutely weakly normal exactly when some
affine open cover has absolutely weakly normal section rings. -/
@[stacks 0EUP]
#check (AlgebraicGeometry.Scheme.hasRingPropertyLocally_iff_exists_affineOpenCover_sectionsRing X
    (fun A : CommRingCat.{u} ↦ AbsolutelyWeaklyNormalRing A) :
  AlgebraicGeometry.Scheme.AbsolutelyWeaklyNormal X ↔
    ∃ 𝒰 : X.AffineOpenCover,
      ∀ i : 𝒰.I₀, AbsolutelyWeaklyNormalRing (Γ(X, (𝒰.f i).opensRange)))

/- Lemma 29.47.4 (7): a scheme is absolutely weakly normal exactly when some
open cover consists of absolutely weakly normal open subschemes. -/
@[stacks 0EUP]
#check (AlgebraicGeometry.Scheme.hasRingPropertyLocally_iff_exists_openCover_by_hasRingPropertyLocally X
    (fun A : CommRingCat.{u} ↦ AbsolutelyWeaklyNormalRing A) :
  AlgebraicGeometry.Scheme.AbsolutelyWeaklyNormal X ↔
    ∃ 𝒰 : X.OpenCover,
      ∀ i : 𝒰.I₀,
        AlgebraicGeometry.Scheme.AbsolutelyWeaklyNormal ((𝒰.f i).opensRange).toScheme)

/- Lemma 29.47.4 (8): absolute weak normality restricts to every open
subscheme. -/
@[stacks 0EUP]
#check (AlgebraicGeometry.Scheme.hasRingPropertyLocally_toScheme
    (X := X) (P := fun A : CommRingCat.{u} ↦ AbsolutelyWeaklyNormalRing A) :
  AlgebraicGeometry.Scheme.AbsolutelyWeaklyNormal X →
    ∀ U : X.Opens, AlgebraicGeometry.Scheme.AbsolutelyWeaklyNormal U.toScheme)
