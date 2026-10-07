module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact

/-!
# Quasi-compact fibre products of schemes over an algebraic space

Fibre products of morphisms from quasi-compact or affine schemes into an algebraic space may be
tested for quasi-compactness in `AlgebraicSpace S`.
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
  sorry

namespace forallQuasiCompactPullback

/-- The universal quasi-compact-scheme pullback condition witnesses
`forallQuasiCompactPullback X`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h : ∀ (U V : Over S) [CompactSpace U.left] [CompactSpace V.left]
      (f : ofOver U ⟶ X) (g : ofOver V ⟶ X), IsQuasiCompact (pullback f g)) :
    forallQuasiCompactPullback X :=
  sorry

/-- If `forallQuasiCompactPullback X`, then the fibre product of morphisms from quasi-compact
schemes to `X` is quasi-compact. -/
theorem apply {S : Scheme.{u}} {X : AlgebraicSpace S} (h : forallQuasiCompactPullback X)
    {U V : Over S} [CompactSpace U.left] [CompactSpace V.left]
    (f : ofOver U ⟶ X) (g : ofOver V ⟶ X) :
    IsQuasiCompact (pullback f g) :=
  sorry

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
  sorry

namespace forallAffineQuasiCompactPullback

/-- The universal affine-scheme pullback condition witnesses
`forallAffineQuasiCompactPullback X`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h : ∀ (U V : Over S) [IsAffine U.left] [IsAffine V.left]
      (f : ofOver U ⟶ X) (g : ofOver V ⟶ X), IsQuasiCompact (pullback f g)) :
    forallAffineQuasiCompactPullback X :=
  sorry

/-- If `forallAffineQuasiCompactPullback X`, then the fibre product of morphisms from affine
schemes to `X` is quasi-compact. -/
theorem apply {S : Scheme.{u}} {X : AlgebraicSpace S} (h : forallAffineQuasiCompactPullback X)
    {U V : Over S} [IsAffine U.left] [IsAffine V.left]
    (f : ofOver U ⟶ X) (g : ofOver V ⟶ X) :
    IsQuasiCompact (pullback f g) :=
  sorry

end forallAffineQuasiCompactPullback

end AlgebraicGeometry.AlgebraicSpace
