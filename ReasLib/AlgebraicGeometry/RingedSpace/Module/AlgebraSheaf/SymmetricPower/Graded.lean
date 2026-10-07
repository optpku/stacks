module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SymmetricPower.Graded
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.SymmetricPower.Multiplication
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The graded symmetric algebra on a ringed space

This facade packages the homogeneous symmetric powers and their multiplication as an ordinarily
commutative graded algebra sheaf. Consumers needing only fixed degrees or multiplication can import
the corresponding narrower owner.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.SymmetricPower

/-- Symmetric powers form their canonical ordinarily commutative graded algebra sheaf. -/
@[stacks 01CF "symmetric algebra sheaf"]
noncomputable abbrev graded {X : RingedSpace.{u}} (F : X.Modules) :
    SheafOfModules.RingedSite.GradedAlgebraSheaf
      (J := Opens.grothendieckTopology X) X.sheaf ℕ :=
  SheafOfModules.RingedSite.SymmetricPower.graded
    (J := Opens.grothendieckTopology X) X.sheaf F

end AlgebraicGeometry.RingedSpace.SymmetricPower
