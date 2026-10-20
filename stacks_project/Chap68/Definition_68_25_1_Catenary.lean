module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Catenary

/-!
# Catenary algebraic spaces

An algebraic space is catenary when its canonical space of points is catenary.
-/

@[expose] public section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.IsCatenary :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.AlgebraicSpace S → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.isCatenary_iff :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    AlgebraicGeometry.AlgebraicSpace.IsCatenary X ↔
      TopologicalSpace.CatenarySpace (AlgebraicGeometry.AlgebraicSpace.Points X))

#check (AlgebraicGeometry.AlgebraicSpace.isCatenary_ofOver_iff :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (U : CategoryTheory.Over S),
    AlgebraicGeometry.AlgebraicSpace.IsCatenary (AlgebraicGeometry.AlgebraicSpace.ofOver U) ↔
      TopologicalSpace.CatenarySpace U.left)

#check (AlgebraicGeometry.AlgebraicSpace.instIsCatenary_ofOver :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (U : CategoryTheory.Over S)
    [TopologicalSpace.CatenarySpace U.left],
    AlgebraicGeometry.AlgebraicSpace.IsCatenary (AlgebraicGeometry.AlgebraicSpace.ofOver U))
