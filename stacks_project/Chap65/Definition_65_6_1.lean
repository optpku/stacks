module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Presheaf
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Definition 65.6.1: an algebraic space over a scheme `S` is a presheaf
`F : (Over S)ᵒᵖ ⥤ Type` that is an fppf sheaf, whose diagonal `F ⟶ F ⨯ F` is
representable, and that admits a scheme `U` over `S` with a map
`yoneda.obj U ⟶ F` which is surjective and étale. -/
@[stacks 025Y] #check (AlgebraicGeometry.IsAlgebraicSpace :
  {S : AlgebraicGeometry.Scheme.{u}} → (CategoryTheory.Over S)ᵒᵖ ⥤ Type u → Prop)
