/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.JacobsonSpace
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap68.Definition_68_11_2_ResidueField

/-!
# Closed points of decent algebraic spaces

A closed point of a decent algebraic space is represented by a closed immersion
from the spectrum of a field, equivalently by the residue-field morphism
`X.fromSpecResidueField x`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.14.6: Let `S` be a scheme. Suppose `X` is a decent algebraic space over `S`.
Let `x ∈ |X|` be a closed point. Then `x` can be represented by a closed immersion
`i : Spec(k) ⟶ X` from the spectrum of a field. -/
@[stacks 0AHB]
theorem isClosedImmersion_fromSpecResidueField {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] {x : Points X} (hx : x ∈ closedPoints (Points X)) :
    IsClosedImmersion (X.fromSpecResidueField x) :=
  sorry

/-- A closed point of a decent algebraic space is represented by some closed immersion
`Spec(k) ⟶ X` from the spectrum of a field. -/
theorem exists_fieldValuedPoint_isClosedImmersion {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] {x : Points X} (hx : x ∈ closedPoints (Points X)) :
    ∃ p : FieldValuedPoint X, IsClosedImmersion p.hom ∧ Points.mk p = x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
