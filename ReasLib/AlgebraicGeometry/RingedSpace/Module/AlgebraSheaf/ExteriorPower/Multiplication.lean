module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.Multiplication
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.ExteriorPower
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Multiplication of exterior-power sheaves on ringed spaces

The unit and homogeneous multiplication are thin specializations of the commutative-ringed-site
construction. The degreewise exterior-power functor remains independently importable.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ExteriorPower

/-- The degree-zero unit of the exterior-power algebra on a ringed space. -/
@[stacks 01CF "unit of the exterior-power algebra"]
noncomputable abbrev one {X : RingedSpace.{u}} (F : X.Modules) :
    SheafOfModules.unit X.ringCatSheaf ⟶ sheaf F 0 :=
  SheafOfModules.RingedSite.ExteriorPower.one X.sheaf F

/-- Multiplication between two homogeneous exterior powers on a ringed space. -/
@[stacks 01CF "multiplication of exterior powers"]
noncomputable abbrev mul {X : RingedSpace.{u}} (F : X.Modules) (n m : ℕ) :
    CategoryTheory.MonoidalCategory.tensorObj (sheaf F n) (sheaf F m) ⟶
      sheaf F (n + m) :=
  SheafOfModules.RingedSite.ExteriorPower.mul X.sheaf F n m

end AlgebraicGeometry.RingedSpace.ExteriorPower
