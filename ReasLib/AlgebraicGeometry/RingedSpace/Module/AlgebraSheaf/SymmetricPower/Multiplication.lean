/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SymmetricPower.Multiplication
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.SymmetricPower
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Multiplication of symmetric-power sheaves on ringed spaces

The degree-zero unit and homogeneous multiplication specialize the corresponding construction on
an arbitrary commutative ringed site. The degreewise symmetric-power functor remains independently
importable.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.SymmetricPower

/-- The degree-zero unit of the symmetric algebra sheaf on a ringed space. -/
@[stacks 01CF "symmetric algebra sheaf unit"]
noncomputable abbrev one {X : RingedSpace.{u}} (F : X.Modules) :
    SheafOfModules.unit X.ringCatSheaf ⟶ sheaf F 0 :=
  SheafOfModules.RingedSite.SymmetricPower.one X.sheaf F

/-- Multiplication between two homogeneous symmetric powers on a ringed space. -/
@[stacks 01CF "symmetric algebra sheaf multiplication"]
noncomputable abbrev mul {X : RingedSpace.{u}} (F : X.Modules) (n m : ℕ) :
    CategoryTheory.MonoidalCategory.tensorObj (sheaf F n) (sheaf F m) ⟶
      sheaf F (n + m) :=
  SheafOfModules.RingedSite.SymmetricPower.mul X.sheaf F n m

end AlgebraicGeometry.RingedSpace.SymmetricPower
