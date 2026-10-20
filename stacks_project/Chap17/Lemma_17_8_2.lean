module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous.LocalGeneration
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Site
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace.Hom

universe u

/- Lemma 17.8.2 (01B3): pullback along a morphism of ringed spaces preserves local generation
by sections. -/
@[stacks 01B3]
#check fun {X Y : RingedSpace.{u}} (f : X ⟶ Y) (G : Y.Modules)
    [SheafOfModules.IsLocallyGeneratedBySections G] ↦
  (inferInstance :
    SheafOfModules.IsLocallyGeneratedBySections ((pullback f).obj G))
