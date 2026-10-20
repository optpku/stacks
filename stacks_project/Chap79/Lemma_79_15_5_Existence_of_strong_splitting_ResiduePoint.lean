module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.ResiduePoint

/-! # Residue-field points of the finite-part localization -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.GroupoidScheme.residueMap :
  ∀ {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left),
    ofOver (GroupoidScheme.residueOver G u) ⟶ ofOver G.U)

#check (AlgebraicGeometry.GroupoidScheme.strongSplittingHom :
  ∀ {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left)
    [GroupoidScheme.StrongSplitting G u],
    ofOver (GroupoidScheme.residueOver G u) ⟶
      (GroupoidAlgebraicSpace.finitePart (GroupoidAlgebraicSpace.ofScheme G)).U.left)

#check (AlgebraicGeometry.GroupoidScheme.strongSplittingHom_liesOver :
  ∀ {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left)
    [GroupoidScheme.StrongSplitting G u],
    GroupoidScheme.strongSplittingHom G u ≫
        GroupoidAlgebraicSpace.finitePartToU (GroupoidAlgebraicSpace.ofScheme G) =
      GroupoidScheme.residueMap G u)
