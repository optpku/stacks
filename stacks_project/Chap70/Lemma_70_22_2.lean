/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_18_1_Dominant
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap70.Lemma_70_22_2_DvrAlong

/-!
# Refined Noetherian DVR valuative criterion for separatedness

A locally finite-type quasi-separated morphism of algebraic spaces into a
locally Noetherian target is separated as soon as every DVR valuative square
whose generic arrow factors through a dense finite-type morphism has at most
one dotted lift.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ValuativeCriterion.DVR.Along

/-- Lemma 70.22.2: Let `S` be a scheme. Let `f : X ⟶ Y` and `h : U ⟶ X` be
morphisms of algebraic spaces over `S`. Assume that `Y` is locally Noetherian,
that `f` is locally of finite type and quasi-separated, that `h` is of finite
type, and that the image of `|h| : |U| ⟶ |X|` is dense in `|X|`. If given any
commutative solid diagram `Spec(K) ⟶ U ⟶ X` over `Spec(A) ⟶ Y` where `A` is a
discrete valuation ring with field of fractions `K`, there exists at most one
dotted arrow making the diagram commute, then `f` is separated. -/
@[stacks 0CME]
theorem separated_of_uniqueness {S : Scheme.{u}} {U X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (h : U ⟶ X) [IsLocallyNoetherian Y] [LocallyOfFiniteType f]
    [QuasiSeparated f] [FiniteType h] [Dominant h]
    (h_uniqueness : Uniqueness h f) : Separated f :=
  sorry

end ValuativeCriterion.DVR.Along

end AlgebraicGeometry.AlgebraicSpace
