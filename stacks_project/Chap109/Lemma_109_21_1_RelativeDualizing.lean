/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.RightAdjoint
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.StructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.TensorPower
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.AtWorstNodal

/-!
# Relative dualizing sheaf of a family of curves

The relative dualizing sheaf of a morphism is the degree `-1` cohomology of the
chosen right adjoint of derived pushforward applied to the derived structure
sheaf of the base. Integral tensor powers of this sheaf carry the canonical
pullback-pushforward counit.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- The relative dualizing sheaf of a morphism, as the degree `-1` cohomology of
the chosen relative dualizing complex. -/
noncomputable def relativeDualizingSheaf {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [(pushforwardCohomologyIn f).IsLeftAdjoint] : X.Modules :=
  RingedSpace.ModuleDerived.cohomologySheaf
    ((pushforwardCohomologyIn f).rightAdjoint.obj (structureSheaf S)).obj
    (-1)

/-- The relative dualizing sheaf is the degree `-1` cohomology of the chosen
right adjoint of derived pushforward on the derived structure sheaf. -/
theorem relativeDualizingSheaf_eq {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [(pushforwardCohomologyIn f).IsLeftAdjoint] :
    relativeDualizingSheaf f =
      RingedSpace.ModuleDerived.cohomologySheaf
        ((pushforwardCohomologyIn f).rightAdjoint.obj (structureSheaf S)).obj
        (-1) :=
  sorry

/-- For an at-worst-nodal proper morphism, the relative dualizing sheaf is
invertible. -/
instance instInvertible_relativeDualizingSheaf {X S : Scheme.{u}} (f : X ⟶ S)
    [AtWorstNodal f] [IsProper f] [(pushforwardCohomologyIn f).IsLeftAdjoint] :
    Modules.Invertible (relativeDualizingSheaf f) :=
  sorry

/-- The adjunction counit `(pullback f).obj ((pushforward f).obj
(tensorPowerInt (relativeDualizingSheaf f) m)) ⟶
tensorPowerInt (relativeDualizingSheaf f) m`. -/
noncomputable def dualizingTensorPowerCounit {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [(pushforwardCohomologyIn f).IsLeftAdjoint]
    [Modules.Invertible (relativeDualizingSheaf f)] (m : ℕ) :
    (Modules.pullback f).obj
        ((Modules.pushforward f).obj
          (Modules.tensorPowerInt (relativeDualizingSheaf f) (m : ℤ))) ⟶
      Modules.tensorPowerInt (relativeDualizingSheaf f) (m : ℤ) :=
  (Modules.pullbackPushforwardAdjunction f).counit.app _

/-- `dualizingTensorPowerCounit` is the pullback-pushforward counit at
`tensorPowerInt (relativeDualizingSheaf f) m`. -/
theorem dualizingTensorPowerCounit_eq {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [(pushforwardCohomologyIn f).IsLeftAdjoint]
    [Modules.Invertible (relativeDualizingSheaf f)] (m : ℕ) :
    dualizingTensorPowerCounit f m =
      (Modules.pullbackPushforwardAdjunction f).counit.app
        (Modules.tensorPowerInt (relativeDualizingSheaf f) (m : ℤ)) :=
  sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
