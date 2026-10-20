module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealPower.Restriction

/-! Compatibility bridge for the canonical algebraic-space ideal-power API. -/

@[expose]
public section

open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

#check (idealPowerProductHomStage :
  IdealSubobject X → X.Modules → X.Modules → ℕ → AddCommGrpCat.{u + 1})

end AlgebraicGeometry.AlgebraicSpace.Modules
