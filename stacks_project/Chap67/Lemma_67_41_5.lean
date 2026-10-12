/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_41_1_ValuativeCriterion

/-!
# Separated morphisms and the existence part of the valuative criterion

For a separated morphism of algebraic spaces, the existence part of the
valuative criterion is equivalent to the scheme-style existence of a dotted
arrow in every valuative square.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace ValuativeCriterion.Existence

/-- Lemma 67.41.5: Let `S` be a scheme. Let `f : X ⟶ Y` be a separated morphism
of algebraic spaces over `S`. Then `f` satisfies the existence part of the
valuative criterion as in Definition 67.41.1 if and only if, given any
commutative solid diagram `Spec(K) ⟶ X` over `Spec(A) ⟶ Y` where `A` is a
valuation ring with field of fractions `K`, there exists a dotted arrow
`Spec(A) ⟶ X`, i.e., `f` satisfies the existence part of the valuative
criterion as in Schemes, Definition 26.20.3
(`AlgebraicGeometry.ValuativeCriterion.Existence`). -/
@[stacks 0A3W]
theorem iff_hasLift_of_separated {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [Separated f] : Existence f ↔ ∀ sq : ValuativeCommSq f, sq.commSq.HasLift :=
  sorry

/-- If a separated morphism of algebraic spaces satisfies the existence part of
the valuative criterion, then every valuative square admits a dotted arrow. -/
theorem hasLift_of_separated {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [Separated f] [Existence f] (sq : ValuativeCommSq f) : sq.commSq.HasLift :=
  sorry

end ValuativeCriterion.Existence
end AlgebraicGeometry.AlgebraicSpace
