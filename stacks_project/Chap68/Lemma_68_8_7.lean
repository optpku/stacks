module

public import Mathlib.Topology.Constructible
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap66.Lemma_66_8_1_Constructible

/-!
# Étale-local and topological constructibility on quasi-separated algebraic spaces

For a quasi-separated algebraic space, étale-local constructibility of a subset of `|X|`
is equivalent to local constructibility in the topological space of points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Topology

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.8.7: Let `S` be a scheme. Let `X` be a quasi-separated algebraic space over `S`.
Let `E ⊂ |X|` be a subset. Then `E` is étale locally constructible if and only if `E` is a
locally constructible subset of the topological space `|X|`. -/
@[stacks 0ECZ]
theorem isEtaleLocallyConstructible_iff_isLocallyConstructible
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsAbsolutelyQuasiSeparated X]
    (E : Set (Points X)) :
    IsEtaleLocallyConstructible E ↔ IsLocallyConstructible E :=
  sorry

/-- On a quasi-separated algebraic space, an étale locally constructible subset of `|X|` is
locally constructible in the topological space of points. -/
theorem isLocallyConstructible_of_isEtaleLocallyConstructible
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsAbsolutelyQuasiSeparated X]
    (E : Set (Points X)) :
    IsEtaleLocallyConstructible E → IsLocallyConstructible E :=
  sorry

/-- On a quasi-separated algebraic space, a locally constructible subset of `|X|` is étale
locally constructible. -/
theorem isEtaleLocallyConstructible_of_isLocallyConstructible
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsAbsolutelyQuasiSeparated X]
    (E : Set (Points X)) :
    IsLocallyConstructible E → IsEtaleLocallyConstructible E :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
