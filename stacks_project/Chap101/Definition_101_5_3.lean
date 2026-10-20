module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.RelativeIsom.Automorphisms
public import ReasLib.AlgebraicGeometry.AlgebraicStack.RelativeIsom.Group
public import ReasLib.AlgebraicGeometry.AlgebraicStack.RelativeIsom.Construction
import ReasLib.AlgebraicGeometry.AlgebraicStack.Base
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Definition 101.5.3 (1): relative automorphisms of `x : Z ⟶ X`
are the pullback `Z ×_{x, X} I_{X/Y}`. -/
@[stacks 06PP] #check (AlgebraicGeometry.AlgebraicStack.RelativeIsom.relativeAut :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X), GroupoidsOver S)

/- Definition 101.5.3 (1): relative automorphisms form a group
algebraic space over `Z` by pulling back composition on relative inertia. -/
@[stacks 06PP] #check (AlgebraicGeometry.AlgebraicStack.RelativeIsom.instGrpObj_asHomotopy :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X), GrpObj (AlgebraicGeometry.AlgebraicStack.RelativeIsom.asHomotopy f x))

/- Definition 101.5.3 (2): the relative isomorphism sheaf associated
to `α : x1 ≫ f ≅ x2 ≫ f` is `(Z ×_X Z) ×_{Z ×_Y Z, Δ^α} Z`. -/
@[stacks 06PP] #check (AlgebraicGeometry.AlgebraicStack.RelativeIsom.relativeIsom :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {Z : AlgebraicSpace S} {x1 x2 : Z.toGroupoids ⟶ X}
    (α : x1 ≫ f ≅ x2 ≫ f), GroupoidsOver S)

/- Definition 101.5.3 (3): over the identity fibration, relative
automorphisms are written `Isom_X(x, x)`. -/
@[stacks 06PP] #check (AlgebraicGeometry.AlgebraicStack.RelativeIsom.aut :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X), GroupoidsOver S)

/- Definition 101.5.3 (3): over the identity fibration, relative
isomorphisms are written `Isom_X(x1, x2)`. -/
@[stacks 06PP] #check (AlgebraicGeometry.AlgebraicStack.RelativeIsom.isom :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Z : AlgebraicSpace S} (x1 x2 : Z.toGroupoids ⟶ X), GroupoidsOver S)

/- Definition 101.5.3 (3): for an algebraic-space target, use the
absolute terminology sheaf of automorphisms. -/
@[stacks 06PP] #check (AlgebraicGeometry.AlgebraicStack.RelativeIsom.autOn :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Y Z : AlgebraicSpace S} (f : X ⟶ Y.toGroupoids)
    (x : Z.toGroupoids ⟶ X), GroupoidsOver S)

/- Definition 101.5.3 (3): for an algebraic-space target, use the
absolute terminology sheaf of isomorphisms. -/
@[stacks 06PP] #check (AlgebraicGeometry.AlgebraicStack.RelativeIsom.isomOn :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Y Z : AlgebraicSpace S} {x1 x2 : Z.toGroupoids ⟶ X}
    {f : X ⟶ Y.toGroupoids} (α : x1 ≫ f ≅ x2 ≫ f), GroupoidsOver S)
