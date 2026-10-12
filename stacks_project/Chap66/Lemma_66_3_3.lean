/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Lemma_66_3_3_Pullback

/-!
# Characterizations of absolutely quasi-separated algebraic spaces

Lemma 66.3.3 records that absolute quasi-separatedness of an algebraic space is equivalent to
quasi-compactness of fibre products of morphisms from quasi-compact schemes, and equivalently
from affine schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsAbsolutelyQuasiSeparated

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/-- Lemma 66.3.3: for a scheme `S` and an algebraic space `X` over `S`, the following are
equivalent: `X` is absolutely quasi-separated; every fibre product of morphisms from
quasi-compact schemes to `X` is quasi-compact; and every fibre product of morphisms from
affine schemes to `X` is quasi-compact. -/
@[stacks 0AHR]
theorem tfae :
    List.TFAE [IsAbsolutelyQuasiSeparated X, forallQuasiCompactPullback X,
      forallAffineQuasiCompactPullback X] :=
  sorry

/-- An algebraic space is absolutely quasi-separated iff fibre products of morphisms from
quasi-compact schemes are quasi-compact. -/
theorem iff_forallQuasiCompactPullback :
    IsAbsolutelyQuasiSeparated X ↔ forallQuasiCompactPullback X :=
  sorry

/-- An algebraic space is absolutely quasi-separated iff fibre products of morphisms from affine
schemes are quasi-compact. -/
theorem iff_forallAffineQuasiCompactPullback :
    IsAbsolutelyQuasiSeparated X ↔ forallAffineQuasiCompactPullback X :=
  sorry

end IsAbsolutelyQuasiSeparated

end AlgebraicGeometry.AlgebraicSpace
