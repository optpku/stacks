/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.MonoidalCategory.TensorPower
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal

/-!
# Tensor powers of modules on algebraic spaces

Integral tensor powers of `𝒪_X`-modules are the monoidal-category tensor powers based at the
unit of `AlgebraicGeometry.AlgebraicSpace.Modules.instMonoidalCategory`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The tensor power of an `𝒪_X`-module, based at the monoidal unit of `X.Modules`. -/
noncomputable def tensorPowerInt (L : X.Modules) (d : ℕ) : X.Modules :=
  tensorPowerWithDegreeZero (𝟙_ X.Modules) L d

/-- `tensorPowerInt L d` is `tensorPowerWithDegreeZero` at the monoidal unit of `X.Modules`. -/
theorem tensorPowerInt_eq (L : X.Modules) (d : ℕ) :
    tensorPowerInt L d = tensorPowerWithDegreeZero (𝟙_ X.Modules) L d :=
  rfl

/-- The twist of a module by a tensor power of another module. -/
noncomputable def twist (F L : X.Modules) (d : ℕ) : X.Modules :=
  tensorObj F (tensorPowerInt L d)

/-- `twist F L d` is the tensor product of `F` with `tensorPowerInt L d`. -/
theorem twist_eq (F L : X.Modules) (d : ℕ) :
    twist F L d = tensorObj F (tensorPowerInt L d) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Modules
