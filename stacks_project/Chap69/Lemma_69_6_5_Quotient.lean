module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FreeQuotient.Torsor

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
universe u

#check (AlgebraicGeometry.AlgebraicSpace.IsFreeQuotient :
  ∀ {S : Scheme.{u}} {W U : AlgebraicSpace S} {G : Type u} [Group G],
    (G →* Aut W) → (W ⟶ U) → Prop)
