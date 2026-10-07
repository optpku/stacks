module

public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_18_1_Dominant
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap70.Lemma_70_22_1_DvrAlong

/-!
# Refined Noetherian DVR valuative criterion for properness

A finite-type separated morphism of algebraic spaces into a locally Noetherian
target is proper as soon as every DVR valuative square whose generic arrow
factors through a dense finite-type morphism admits a dotted lift.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ValuativeCriterion.DVR.Along

/-- Lemma 70.22.1: Let `S` be a scheme. Let `f : X ⟶ Y` and `h : U ⟶ X` be
morphisms of algebraic spaces over `S`. Assume that `Y` is locally Noetherian,
that `f` and `h` are of finite type, that `f` is separated, and that the image
of `|h| : |U| ⟶ |X|` is dense in `|X|`. If given any commutative solid diagram
`Spec(K) ⟶ U ⟶ X` over `Spec(A) ⟶ Y` where `A` is a discrete valuation ring
with field of fractions `K`, there exists a dotted arrow making the diagram
commute, then `f` is proper. -/
@[stacks 0CMD]
theorem proper_of_separated {S : Scheme.{u}} {U X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (h : U ⟶ X) [IsLocallyNoetherian Y] [FiniteType f]
    [FiniteType h] [Separated f] [Dominant h]
    (h_existence : Existence h f) : Proper f :=
  sorry

end ValuativeCriterion.DVR.Along

end AlgebraicGeometry.AlgebraicSpace
