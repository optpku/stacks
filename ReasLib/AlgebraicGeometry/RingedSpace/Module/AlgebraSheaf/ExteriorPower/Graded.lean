module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.Graded
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.ExteriorPower.Multiplication
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The graded exterior algebra on a ringed space

This compatibility facade packages the homogeneous exterior powers and their multiplication as
a sectionwise graded algebra sheaf. Consumers needing only fixed exterior degrees or multiplication
can import the corresponding narrower owner.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ExteriorPower

/-- The naturally graded exterior algebra of a module sheaf on a ringed space. -/
@[stacks 01CF "graded exterior algebra on a ringed space"]
noncomputable abbrev graded {X : RingedSpace.{u}} (F : X.Modules) :
    SheafOfModules.RingedSite.GradedAlgebraSheaf
      (J := Opens.grothendieckTopology X) X.sheaf ℕ :=
  SheafOfModules.RingedSite.ExteriorPower.graded
    (J := Opens.grothendieckTopology X) X.sheaf F

end AlgebraicGeometry.RingedSpace.ExteriorPower
