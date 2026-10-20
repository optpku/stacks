/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact

/-!
# Quasi-compact fibre products and absolute quasi-separatedness

An algebraic space is absolutely quasi-separated exactly when fibre products of morphisms
from quasi-compact schemes are quasi-compact, equivalently when this holds for affine schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Fibre products of morphisms from quasi-compact schemes to `X` are quasi-compact algebraic
spaces. -/
def forallQuasiCompactPullback {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop :=
  ∀ (U V : Over S) [CompactSpace U.left] [CompactSpace V.left]
    (f : ofOver U ⟶ X) (g : ofOver V ⟶ X),
    IsQuasiCompact (pullback f g)

/-- `forallQuasiCompactPullback X` means that fibre products of quasi-compact schemes over `X`
are quasi-compact. -/
theorem forallQuasiCompactPullback_iff {S : Scheme.{u}} (X : AlgebraicSpace S) :
    forallQuasiCompactPullback X ↔
      ∀ (U V : Over S) [CompactSpace U.left] [CompactSpace V.left]
        (f : ofOver U ⟶ X) (g : ofOver V ⟶ X),
        IsQuasiCompact (pullback f g) :=
  Iff.rfl

namespace forallQuasiCompactPullback

/-- The universal quasi-compact-scheme pullback condition witnesses
`forallQuasiCompactPullback X`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h : ∀ (U V : Over S) [CompactSpace U.left] [CompactSpace V.left]
      (f : ofOver U ⟶ X) (g : ofOver V ⟶ X), IsQuasiCompact (pullback f g)) :
    forallQuasiCompactPullback X :=
  h

/-- If `forallQuasiCompactPullback X`, then the fibre product of morphisms from quasi-compact
schemes to `X` is quasi-compact. -/
theorem apply {S : Scheme.{u}} {X : AlgebraicSpace S} (h : forallQuasiCompactPullback X)
    {U V : Over S} [CompactSpace U.left] [CompactSpace V.left]
    (f : ofOver U ⟶ X) (g : ofOver V ⟶ X) :
    IsQuasiCompact (pullback f g) :=
  h U V f g

end forallQuasiCompactPullback

/-- Fibre products of morphisms from affine schemes to `X` are quasi-compact algebraic spaces. -/
def forallAffineQuasiCompactPullback {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop :=
  ∀ (U V : Over S) [IsAffine U.left] [IsAffine V.left]
    (f : ofOver U ⟶ X) (g : ofOver V ⟶ X),
    IsQuasiCompact (pullback f g)

/-- `forallAffineQuasiCompactPullback X` means that fibre products of affine schemes over `X`
are quasi-compact. -/
theorem forallAffineQuasiCompactPullback_iff {S : Scheme.{u}} (X : AlgebraicSpace S) :
    forallAffineQuasiCompactPullback X ↔
      ∀ (U V : Over S) [IsAffine U.left] [IsAffine V.left]
        (f : ofOver U ⟶ X) (g : ofOver V ⟶ X),
        IsQuasiCompact (pullback f g) :=
  Iff.rfl

namespace forallAffineQuasiCompactPullback

/-- The universal affine-scheme pullback condition witnesses
`forallAffineQuasiCompactPullback X`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h : ∀ (U V : Over S) [IsAffine U.left] [IsAffine V.left]
      (f : ofOver U ⟶ X) (g : ofOver V ⟶ X), IsQuasiCompact (pullback f g)) :
    forallAffineQuasiCompactPullback X :=
  h

/-- If `forallAffineQuasiCompactPullback X`, then the fibre product of morphisms from affine
schemes to `X` is quasi-compact. -/
theorem apply {S : Scheme.{u}} {X : AlgebraicSpace S} (h : forallAffineQuasiCompactPullback X)
    {U V : Over S} [IsAffine U.left] [IsAffine V.left]
    (f : ofOver U ⟶ X) (g : ofOver V ⟶ X) :
    IsQuasiCompact (pullback f g) :=
  h U V f g

end forallAffineQuasiCompactPullback

namespace IsAbsolutelyQuasiSeparated

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/-- Absolute quasi-separatedness of an algebraic space is equivalent to quasi-compactness of
all fibre products of morphisms from quasi-compact schemes, equivalently from affine schemes. -/
theorem tfae :
    List.TFAE [IsAbsolutelyQuasiSeparated X, forallQuasiCompactPullback X,
      forallAffineQuasiCompactPullback X] :=
  sorry

/-- An algebraic space is absolutely quasi-separated iff fibre products of morphisms from
quasi-compact schemes are quasi-compact. -/
theorem iff_forallQuasiCompactPullback :
    IsAbsolutelyQuasiSeparated X ↔ forallQuasiCompactPullback X :=
  (tfae X).out 0 1

/-- An algebraic space is absolutely quasi-separated iff fibre products of morphisms from affine
schemes are quasi-compact. -/
theorem iff_forallAffineQuasiCompactPullback :
    IsAbsolutelyQuasiSeparated X ↔ forallAffineQuasiCompactPullback X :=
  (tfae X).out 0 2

end IsAbsolutelyQuasiSeparated

end AlgebraicGeometry.AlgebraicSpace
