module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap66.Lemma_66_10_3_LocalRingDim
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap67.Lemma_67_49_1_FiniteComponents
public import stacks_project.Chap68.Definition_68_22_1_GenericPoints

/-!
# Codimension-zero points of quasi-separated algebraic spaces

On a quasi-separated algebraic space, being a point of codimension `0`, having
local-ring dimension `0`, and being a generic point of an irreducible component
of `|X|` are equivalent, and any such point lies in an open subspace which is a
scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 72.9.2 (1): Let `S` be a scheme. Let `X` be a quasi-separated algebraic
space over `S`. Let `x ∈ |X|`. The following are equivalent: `x` is a point of
codimension `0` on `X`, the local ring of `X` at `x` has dimension `0`, and `x`
is a generic point of an irreducible component of `|X|`. -/
@[stacks 0ADC]
theorem codimZero_tfae {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsAbsolutelyQuasiSeparated X] (x : Points X) :
    List.TFAE
      [ x ∈ codimZeroPoints X
      , localRingDimAt x = 0
      , x ∈ genericPoints X ] :=
  sorry

/-- Lemma 72.9.2 (2): Let `S` be a scheme. Let `X` be a quasi-separated algebraic
space over `S`. Let `x ∈ |X|`. If the local ring of `X` at `x` has dimension
`0`, then there exists an open subspace of `X` containing `x` which is a
scheme. -/
@[stacks 0ADC]
theorem exists_open_isScheme_of_localRingDimAt_eq_zero {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsAbsolutelyQuasiSeparated X] (x : Points X)
    (hx : localRingDimAt x = 0) :
    ∃ U : OpenSubspace X, IsScheme U.X ∧ x ∈ U.pointsSet :=
  sorry

/-- On an absolutely quasi-separated algebraic space, a generic point of an
irreducible component of `|X|` lies in an open subspace which is a scheme. -/
theorem exists_open_isScheme_of_mem_genericPoints {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsAbsolutelyQuasiSeparated X] {x : Points X}
    (hx : x ∈ genericPoints X) :
    ∃ U : OpenSubspace X, IsScheme U.X ∧ x ∈ U.pointsSet :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
