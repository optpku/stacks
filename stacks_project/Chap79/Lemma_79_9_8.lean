/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_23_2_GeometricallyUnibranch
public import stacks_project.Chap78.Definition_78_5_1_Group
public import stacks_project.Chap79.Situation_79_9_2_OnField

/-!
# Geometric unibranchness of groups over fields and groupoids on fields

In Situation 79.9.2 the arrow algebraic space of a groupoid on a field is
geometrically unibranch. In Situation 79.9.1 a group algebraic space over a
field is geometrically unibranch.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- Lemma 79.9.8 (1): in Situation 79.9.2 the algebraic space `G.R` is
geometrically unibranch. -/
@[stacks 06E4]
theorem isGeometricallyUnibranch {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {k : Type u} [Field k]
    (σ : Spec (.of k) ⟶ S) [IsOnField G σ] :
    AlgebraicSpace.IsGeometricallyUnibranch G.R.left := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace

namespace AlgebraicGeometry.GroupAlgebraicSpace

/-- Lemma 79.9.8 (2): in Situation 79.9.1 the algebraic space `G` is
geometrically unibranch. -/
@[stacks 06E4, instance]
instance instIsGeometricallyUnibranch {S : Scheme.{u}} {k : Type u} [Field k]
    {σ : Spec (.of k) ⟶ S}
    (G : GroupAlgebraicSpace (AlgebraicSpace.ofOver (Over.mk σ))) :
    AlgebraicSpace.IsGeometricallyUnibranch G.X.left := sorry

end AlgebraicGeometry.GroupAlgebraicSpace
