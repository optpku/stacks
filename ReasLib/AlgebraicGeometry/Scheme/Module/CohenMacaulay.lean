module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.CohenMacaulay
public import ReasLib.AlgebraicGeometry.Scheme.Module.Depth

/-!
# Cohen-Macaulay coherent modules on locally Noetherian schemes

This leaf provides the scheme spelling of the generic locally-ringed-space
Cohen-Macaulay module predicate and its stalkwise computation API.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- A coherent module on a locally Noetherian scheme is Cohen-Macaulay when
its stalks are Cohen-Macaulay modules over their local rings. -/
abbrev CohenMacaulay (ℱ : X.Modules) [ℱ.IsCoherent] : Prop :=
  LocallyRingedSpace.Modules.CohenMacaulay (X := X.toLocallyRingedSpace) ℱ

namespace CohenMacaulay

/-- The stalk of a Cohen-Macaulay coherent scheme module is Cohen-Macaulay. -/
theorem stalk
    {ℱ : X.Modules} [ℱ.IsCoherent] [CohenMacaulay ℱ] (x : X) :
    Module.CohenMacaulay (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) := sorry

/-- A Cohen-Macaulay coherent scheme module supplies the Cohen-Macaulay instance at each stalk. -/
instance instStalkCohenMacaulay
    {ℱ : X.Modules} [ℱ.IsCoherent] [CohenMacaulay ℱ] (x : X) :
    Module.CohenMacaulay (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) :=
  stalk x

end CohenMacaulay

variable (ℱ : X.Modules) [ℱ.IsCoherent]

/-- A coherent scheme module is Cohen-Macaulay exactly when all of its stalks satisfy every
local algebraic Serre condition. -/
theorem cohenMacaulay_iff_forall_serreConditionS :
    CohenMacaulay ℱ ↔
      ∀ x : X, ∀ k : ℕ,
        Module.SerreConditionS (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) k := sorry

/-- A coherent scheme module is Cohen-Macaulay exactly when it satisfies every named scheme
module Serre condition. -/
theorem cohenMacaulay_iff_forall_satisfiesSerreConditionS :
    CohenMacaulay ℱ ↔ ∀ k : ℕ, satisfiesSerreConditionS ℱ k := sorry

end AlgebraicGeometry.Scheme.Modules
