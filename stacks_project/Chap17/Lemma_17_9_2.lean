module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous.LocalGeneration
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Site
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 17.9.2 (01B6): pullback along a morphism of ringed spaces preserves finite-type module
sheaves. -/
@[stacks 01B6]
#check fun {X Y : RingedSpace.{u}} (f : X ⟶ Y) (G : Y.Modules) [G.IsFiniteType] ↦
  (inferInstance : ((f^*).obj G).IsFiniteType)
