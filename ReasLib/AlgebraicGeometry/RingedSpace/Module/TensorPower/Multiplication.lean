/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.TensorPower.Multiplication
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorPower
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Multiplication of tensor-power sheaves on ringed spaces

The degree-zero unit and concatenation maps specialize the topology-independent ringed-site
construction. Recursive tensor-power comparisons are kept in the independent `Comparison` leaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.TensorPower

/-- The multiplication morphism from the tensor product of the `n`th and `m`th tensor powers
to `TensorPower.sheaf F (n + m)`. -/
@[stacks 01CF "tensor-power multiplication on a ringed space"]
noncomputable abbrev mul {X : RingedSpace.{u}} (F : X.Modules) (n m : ℕ) :
    CategoryTheory.MonoidalCategory.tensorObj (sheaf F n) (sheaf F m) ⟶
      sheaf F (n + m) :=
  SheafOfModules.RingedSite.TensorPower.mul X.sheaf F n m

/-- The degree-zero unit morphism of tensor powers on a ringed space. -/
@[stacks 01CF "tensor-power unit on a ringed space"]
noncomputable abbrev one {X : RingedSpace.{u}} (F : X.Modules) :
    SheafOfModules.unit X.ringCatSheaf ⟶ sheaf F 0 :=
  SheafOfModules.RingedSite.TensorPower.one X.sheaf F

/-- The canonical comparison from the tensor product of the `m`th and `n`th tensor powers
to `TensorPower.sheaf F (m + n)`. -/
@[stacks 01CF "addition of tensor-power degrees on a ringed space"]
noncomputable abbrev addIso {X : RingedSpace.{u}} (F : X.Modules) :
    (m n : ℕ) → sheaf F m ⊗ sheaf F n ≅ sheaf F (m + n) :=
  SheafOfModules.RingedSite.TensorPower.addIso X.sheaf F

end AlgebraicGeometry.RingedSpace.TensorPower


