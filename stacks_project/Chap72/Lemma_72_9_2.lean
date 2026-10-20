/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.SchematicLocus.CodimensionZero
import StacksCheckRecall

/-!
# Codimension-zero points of quasi-separated algebraic spaces

On a quasi-separated algebraic space, being a point of codimension `0`, having
local-ring dimension `0`, and being a generic point of an irreducible component
of `|X|` are equivalent, and any such point lies in an open subspace which is a
scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 72.9.2 (1): Let `S` be a scheme. Let `X` be a quasi-separated algebraic
space over `S`. Let `x ∈ |X|`. The following are equivalent: `x` is a point of
codimension `0` on `X`, the local ring of `X` at `x` has dimension `0`, and `x`
is a generic point of an irreducible component of `|X|`. -/
@[stacks 0ADC] #check
  (AlgebraicGeometry.AlgebraicSpace.codimZero_tfae :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsAbsolutelyQuasiSeparated X]
      (x : Points X),
      List.TFAE
        [ x ∈ codimZeroPoints X
        , localRingDimAt x = 0
        , x ∈ genericPoints X ])

/- Lemma 72.9.2 (2): Let `S` be a scheme. Let `X` be a quasi-separated algebraic
space over `S`. Let `x ∈ |X|`. If the local ring of `X` at `x` has dimension
`0`, then there exists an open subspace of `X` containing `x` which is a
scheme. -/
@[stacks 0ADC] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_open_isScheme_of_localRingDimAt_eq_zero :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsAbsolutelyQuasiSeparated X]
      (x : Points X),
      localRingDimAt x = 0 →
        ∃ U : OpenSubspace X, IsScheme U.X ∧ x ∈ U.pointsSet)

/- On an absolutely quasi-separated algebraic space, a generic point of an
irreducible component of `|X|` lies in an open subspace which is a scheme. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.exists_open_isScheme_of_mem_genericPoints :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsAbsolutelyQuasiSeparated X]
      {x : Points X},
      x ∈ genericPoints X →
        ∃ U : OpenSubspace X, IsScheme U.X ∧ x ∈ U.pointsSet)
