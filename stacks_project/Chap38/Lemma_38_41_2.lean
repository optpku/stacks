/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.FittingIdeal.Perfect
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped ModuleRestriction ZeroObject

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 38.41.2: a perfect module sheaf of Tor dimension at most one and constant
rank `r` over a scheme-theoretically dense open `U` has, after a `U`-admissible
blowup, a finite locally free quotient of rank `r` whose canonical kernel is perfect,
has Tor dimension at most one, and vanishes over the inverse image of `U`. -/
@[stacks 0EST] #check
  (AlgebraicGeometry.Scheme.Modules.exists_shortExact_afterAdmissibleBlowup :
    ∀ {X : Scheme.{u}} (F : X.Modules) (U : X.Opens) (r : ℕ),
      SheafOfModules.IsPerfect F →
      RingedSpace.ModuleHasTorDimensionLE F 1 →
      schemeTheoreticallyDense U →
      SheafOfModules.IsFiniteLocallyFreeOfRank r (F.over U) →
      ∃ (X' : Scheme.{u}) (b : X' ⟶ X) (Q : X'.Modules)
        (q : (Scheme.Modules.pullback b).obj F ⟶ Q),
        IsAdmissibleBlowup U b ∧
          (ShortComplex.kernelSequence q).ShortExact ∧
          SheafOfModules.IsFiniteLocallyFreeOfRank r Q ∧
          SheafOfModules.IsPerfect (kernel q) ∧
          RingedSpace.ModuleHasTorDimensionLE (kernel q) 1 ∧
          IsZero ((kernel q).over (b ⁻¹ᵁ U)))

end AlgebraicGeometry.Scheme.Modules
