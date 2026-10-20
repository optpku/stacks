module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.OnField.Unibranch
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group.Unibranch
import StacksCheckRecall

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

/- Lemma 79.9.8: the arrow algebraic space of a groupoid on a field and a group algebraic
space over a field are geometrically unibranch. -/
@[stacks 06E4] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.isGeometricallyUnibranch :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {k : Type u} [Field k] (σ : Spec (.of k) ⟶ S) [GroupoidAlgebraicSpace.IsOnField G σ],
    AlgebraicSpace.IsGeometricallyUnibranch G.R.left)

#check (AlgebraicGeometry.GroupAlgebraicSpace.instIsGeometricallyUnibranch :
  ∀ {S : Scheme.{u}} {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (G : GroupAlgebraicSpace (AlgebraicSpace.ofOver (Over.mk σ))),
    AlgebraicSpace.IsGeometricallyUnibranch G.X.left)
