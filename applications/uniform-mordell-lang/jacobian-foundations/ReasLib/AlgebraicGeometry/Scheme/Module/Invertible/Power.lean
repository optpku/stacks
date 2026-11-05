module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorPower
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Invertibility of nonnegative tensor powers

The tensor-power data and its recursion laws are owned by
`RingedSpace.TensorPower`. This leaf records only the scheme-module property
that those canonical powers remain invertible.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

namespace Invertible

/-- An explicit invertibility witness for `L` yields one for every canonical nonnegative tensor
power, without requiring a local instance installation at the call site. -/
@[stacks 01PS "explicit invertibility of tensor powers"]
theorem tensorPower_isInvertible {L : X.Modules} (hL : Invertible L) (n : ℕ) :
    Invertible (RingedSpace.TensorPower.sheaf L n) := sorry

/-- Canonical invertibility instance for nonnegative tensor powers of an invertible scheme
module. -/
@[stacks 01PS "canonical invertibility of tensor powers"]
instance instTensorPowerIsInvertible {L : X.Modules} [Invertible L] (n : ℕ) :
    Invertible (RingedSpace.TensorPower.sheaf L n) :=
  tensorPower_isInvertible (inferInstance : Invertible L) n

end Invertible

end AlgebraicGeometry.Scheme.Modules
