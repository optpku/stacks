/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Definition_67_41_1_ValuativeCriterion

/-!
# Valuative criterion for properness

A finite type quasi-separated morphism of algebraic spaces is proper if and
only if it satisfies the valuative criterion, if and only if every solid
valuative square admits a unique dotted lift.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ValuativeCriterion

/-- Lemma 67.44.1 (Valuative criterion for properness): Let `S` be a scheme. Let
`f : X ⟶ Y` be a morphism of algebraic spaces over `S`. Assume `f` is of finite
type and quasi-separated. Then the following are equivalent: `f` is proper; the
valuative criterion holds as in Definition 67.41.1 (`ValuativeCriterion`); and
given any commutative solid diagram `Spec(K) ⟶ X` over `Spec(A) ⟶ Y` where `A`
is a valuation ring with field of fractions `K`, there exists a unique dotted
arrow `Spec(A) ⟶ X`, i.e., `f` satisfies the valuative criterion as in Schemes,
Definition 26.20.3. -/
@[stacks 0A40]
theorem proper_tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [FiniteType f] [QuasiSeparated f] :
    List.TFAE [Proper f, ValuativeCriterion f,
      ∀ sq : ValuativeCommSq f, sq.commSq.HasLift ∧ Subsingleton sq.commSq.LiftStruct] :=
  sorry

/-- A finite type quasi-separated morphism of algebraic spaces is proper if and
only if it satisfies the valuative criterion. -/
theorem iff_proper {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [FiniteType f] [QuasiSeparated f] :
    Proper f ↔ ValuativeCriterion f :=
  sorry

end ValuativeCriterion

namespace Proper

/-- A finite type quasi-separated morphism of algebraic spaces that satisfies
the valuative criterion is proper. -/
instance of_valuativeCriterion {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [FiniteType f] [QuasiSeparated f] [ValuativeCriterion f] :
    Proper f :=
  sorry

end Proper

end AlgebraicGeometry.AlgebraicSpace
