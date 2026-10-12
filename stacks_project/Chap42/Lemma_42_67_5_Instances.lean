/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Over.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Over.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.Over.BaseChange

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- The structure morphism of a pullback object is locally of finite type. -/
#check (AlgebraicGeometry.LocallyOfFiniteType.instOverPullbackObj :
  ∀ {S S' : Scheme.{u}} (g : S' ⟶ S) (X : Over S)
    [LocallyOfFiniteType X.hom],
    LocallyOfFiniteType ((Over.pullback g).obj X).hom)

/- A flat slice morphism remains flat after canonical base change. -/
#check (AlgebraicGeometry.Flat.instOverPullbackMap :
  ∀ {S S' : Scheme.{u}} (g : S' ⟶ S) {X Y : Over S}
    (f : X ⟶ Y) [Flat f.left],
    Flat ((Over.pullback g).map f).left)

/- A slice morphism retains its fixed relative dimension after canonical base change. -/
#check (AlgebraicGeometry.Scheme.Hom.RelativeDimension.instOverPullbackMap :
  ∀ {S S' : Scheme.{u}} (g : S' ⟶ S) {X Y : Over S}
    (f : X ⟶ Y) (r : ℕ) [Scheme.Hom.RelativeDimension f.left r],
    Scheme.Hom.RelativeDimension ((Over.pullback g).map f).left r)
