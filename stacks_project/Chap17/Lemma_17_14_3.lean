module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Pullback.LocallyFree
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Site
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace.Hom

universe u

/- Lemma 17.14.3 (01C8): pullback along a morphism of ringed spaces preserves locally free
module sheaves. -/
@[stacks 01C8]
#check fun {X Y : RingedSpace.{u}} (f : X ⟶ Y) (G : Y.Modules) [G.IsLocallyFree] ↦
  (inferInstance : ((pullback f).obj G).IsLocallyFree)
