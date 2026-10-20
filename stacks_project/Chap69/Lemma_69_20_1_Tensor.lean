module

public import ReasLib.CategoryTheory.MonoidalCategory.TensorPower
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal

/-!
# Tensor powers of modules on algebraic spaces

Natural tensor powers of `𝒪_X`-modules are the monoidal-category tensor powers based at the
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
  tensorPower L d

/-- The twist of a module by a tensor power of another module. -/
noncomputable def twist (F L : X.Modules) (d : ℕ) : X.Modules :=
  tensorObj F (tensorPowerInt L d)

end AlgebraicGeometry.AlgebraicSpace.Modules
