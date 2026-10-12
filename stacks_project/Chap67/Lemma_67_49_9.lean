/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_26_1_Nagata
public import stacks_project.Chap67.Lemma_67_49_2
public import stacks_project.Chap67.Lemma_67_49_5_Normalization

/-!
# Finiteness of the absolute normalization of a Nagata algebraic space
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The absolute normalization morphism of a Nagata algebraic space is finite. -/
theorem isFinite_normalizationTo_of_isNagata {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsNagata X] : IsFinite X.normalizationTo :=
  sorry

/-- Lemma 67.49.9: let `S` be a scheme, and let `X` be a Nagata algebraic space
over `S`. Then the absolute normalization `ν : X^ν ⟶ X`, namely
`X.normalizationTo : X.normalization ⟶ X`, is finite. -/
@[stacks 0BB5]
instance instIsFiniteNormalizationToOfIsNagata {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsNagata X] : IsFinite X.normalizationTo :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
