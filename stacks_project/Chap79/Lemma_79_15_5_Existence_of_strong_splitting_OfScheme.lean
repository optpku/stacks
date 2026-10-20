module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.OfScheme

/-! # Groupoid schemes as groupoids in algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.ofScheme :
  ∀ {S : Scheme.{u}}, GroupoidScheme S →
    GroupoidAlgebraicSpace (ofOver (Over.mk (𝟙 S))))

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.ofScheme_U :
  ∀ {S : Scheme.{u}} (G : GroupoidScheme S),
    (GroupoidAlgebraicSpace.ofScheme G).U.left = ofOver G.U)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.ofScheme_R :
  ∀ {S : Scheme.{u}} (G : GroupoidScheme S),
    (GroupoidAlgebraicSpace.ofScheme G).R.left = ofOver G.R)
