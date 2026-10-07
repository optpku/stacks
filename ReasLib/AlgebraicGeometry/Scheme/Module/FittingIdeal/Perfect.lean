module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FittingIdeal.Flattening
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.ModulePullback
public import ReasLib.CategoryTheory.ShortComplex.KernelSequence

/-!
# Flattening perfect module sheaves by admissible blowups

A perfect module sheaf of Tor dimension at most one that has constant rank on a
scheme-theoretically dense open admits an admissible blowup with a finite locally free
quotient and a perfect kernel of Tor dimension at most one.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped ModuleRestriction ZeroObject

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A perfect module sheaf of Tor dimension at most one and constant rank `r` over a
scheme-theoretically dense open `U` has, after a `U`-admissible blowup, a finite locally free
quotient of rank `r` whose canonical kernel is perfect, has Tor dimension at most one, and
vanishes over the inverse image of `U`. -/
theorem exists_shortExact_afterAdmissibleBlowup {X : Scheme.{u}} (F : X.Modules)
    (U : X.Opens) (r : ℕ) (hPerfect : SheafOfModules.IsPerfect F)
    (hTor : RingedSpace.ModuleHasTorDimensionLE F 1)
    (hDense : schemeTheoreticallyDense U)
    (hRank : SheafOfModules.IsFiniteLocallyFreeOfRank r (F.over U)) :
    ∃ (X' : Scheme.{u}) (b : X' ⟶ X) (Q : X'.Modules)
      (q : (Scheme.Modules.pullback b).obj F ⟶ Q),
      IsAdmissibleBlowup U b ∧
        (ShortComplex.kernelSequence q).ShortExact ∧
        SheafOfModules.IsFiniteLocallyFreeOfRank r Q ∧
        SheafOfModules.IsPerfect (kernel q) ∧
        RingedSpace.ModuleHasTorDimensionLE (kernel q) 1 ∧
        IsZero ((kernel q).over (b ⁻¹ᵁ U)) := sorry

end AlgebraicGeometry.Scheme.Modules
