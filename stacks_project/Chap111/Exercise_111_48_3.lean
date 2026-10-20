module

public import ReasLib.Algebra.Homology.DerivedCategory.Ext.CupProduct
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Abelian

universe u

variable {X : RingedSpace.{u}} [HasExt.{u} (X.Modules)]

/- Exercise 111.48.3: on a ringed space `X`, the cup-product maps
`Ext G H i × Ext F G j ⟶ Ext F H (i + j)` for `𝒪_X`-modules `F`, `G`, `H`. -/
@[stacks 0DD3] #check
  (CategoryTheory.Abelian.Ext.cupProductHom :
    ∀ (F G H : X.Modules) (i j : ℕ),
      Abelian.Ext.{u, u, u + 1} G H i →+
        Abelian.Ext.{u, u, u + 1} F G j →+ Abelian.Ext.{u, u, u + 1} F H (i + j))

#check
  (CategoryTheory.Abelian.Ext.cupProduct :
    ∀ {F G H : X.Modules} {i j : ℕ},
      Abelian.Ext.{u, u, u + 1} G H i → Abelian.Ext.{u, u, u + 1} F G j →
        Abelian.Ext.{u, u, u + 1} F H (i + j))
