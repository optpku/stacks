module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteType.ClosedSupport
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Support
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry TopologicalSpace

universe u

/- Lemma 17.9.6 (01BA): a finite-type module sheaf on a ringed space has closed support. -/
@[stacks 01BA]
#check fun {X : RingedSpace.{u}} (F : X.Modules) [F.IsFiniteType] ↦
  (SheafOfModules.IsFiniteType.isClosed_support (𝒪 := X.sheaf) F :
    IsClosed (RingedSpace.moduleSupport F))
