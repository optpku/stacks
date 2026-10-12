/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GeneralLinear.GroupScheme
public import ReasLib.AlgebraicGeometry.GroupScheme.Torsor
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Descent

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupScheme

/-- Every torsor under the rank-`n` general linear group scheme is Zariski-locally trivial. -/
theorem generalLinearLocallyTrivial {S : Scheme.{u}} (n : ℕ)
    (X : Mod (Over S)
      (GeneralLinear.baseChange (specULiftZIsTerminal.from S) (ULift.{u} (Fin n))).X)
    (hX : IsTorsor
      (GeneralLinear.baseChange (specULiftZIsTerminal.from S) (ULift.{u} (Fin n))) X) :
    IsLocallyTrivial
      (GeneralLinear.baseChange (specULiftZIsTerminal.from S) (ULift.{u} (Fin n))) X := sorry

end AlgebraicGeometry.GroupScheme
