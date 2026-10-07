module

public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap68.Lemma_68_12_8_Decent
public import stacks_project.Chap78.Definition_78_5_1_Group
public import stacks_project.Chap79.Situation_79_9_2_OnField

/-!
# Decent groups over fields and groupoids on fields are separated

In Situation 79.9.2, if the arrow space of a groupoid in algebraic spaces on a
field is decent, then it is a separated algebraic space. In Situation 79.9.1, if
a group algebraic space over a field is decent, then it is a separated algebraic
space.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- Lemma 79.9.4 (1): in Situation 79.9.2, if the arrow algebraic space `G.R` is
decent, then it is a separated algebraic space. -/
@[stacks 08BH]
theorem isAbsolutelySeparated {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {k : Type u} [Field k]
    (σ : Spec (.of k) ⟶ S) [IsOnField G σ] [AlgebraicSpace.IsDecent G.R.left] :
    AlgebraicSpace.IsAbsolutelySeparated G.R.left := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace

namespace AlgebraicGeometry.GroupAlgebraicSpace

/-- Lemma 79.9.4 (2): in Situation 79.9.1, if the group algebraic space `G` is
decent, then it is a separated algebraic space. -/
@[stacks 08BH, instance]
instance instIsAbsolutelySeparated {S : Scheme.{u}} {k : Type u} [Field k]
    {σ : Spec (.of k) ⟶ S}
    (G : GroupAlgebraicSpace (AlgebraicSpace.ofOver (Over.mk σ)))
    [AlgebraicSpace.IsDecent G.X.left] :
    AlgebraicSpace.IsAbsolutelySeparated G.X.left := sorry

end AlgebraicGeometry.GroupAlgebraicSpace
