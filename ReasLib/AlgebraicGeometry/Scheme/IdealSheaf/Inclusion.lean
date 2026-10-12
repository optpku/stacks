/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The infimum of the ideals on the base whose pullbacks make the closed subscheme
defined by `D₁` contained in the closed subscheme defined by `D₂`. -/
def inclusionIdeal {Y S : Scheme.{u}} (D₁ D₂ : Y.IdealSheafData) (f : Y ⟶ S) :
    S.IdealSheafData :=
  sInf {J : S.IdealSheafData | D₂ ≤ D₁ ⊔ J.comap f}

end AlgebraicGeometry.Scheme.IdealSheafData
