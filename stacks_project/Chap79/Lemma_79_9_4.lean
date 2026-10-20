/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group.Separation.Field
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.OnField.Separation
import StacksCheckRecall

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

/- Lemma 79.9.4: in Situation 79.9.2, a decent arrow algebraic space is
separated. In Situation 79.9.1, a decent group algebraic space over a field is
separated. -/
@[stacks 08BH] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.isAbsolutelySeparated :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {k : Type u} [Field k]
    (σ : Spec (.of k) ⟶ S) [GroupoidAlgebraicSpace.IsOnField G σ]
    [AlgebraicSpace.IsDecent G.R.left], AlgebraicSpace.IsAbsolutelySeparated G.R.left)

/- Lemma 79.9.4 (2): a decent group algebraic space over a field is separated. -/
@[stacks 08BH] #check (AlgebraicGeometry.GroupAlgebraicSpace.instIsAbsolutelySeparated :
  ∀ {S : Scheme.{u}} {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (G : GroupAlgebraicSpace (AlgebraicSpace.ofOver (Over.mk σ)))
    [AlgebraicSpace.IsDecent G.X.left], AlgebraicSpace.IsAbsolutelySeparated G.X.left)
