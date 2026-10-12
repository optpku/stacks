/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Filtration.CartierRank

/-!
# Cartier-rank filtrations after an admissible blowup
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped ModuleRestriction ZeroObject

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

namespace CartierRankFiltrations

/-- A perfect scheme module of Tor dimension at most one which vanishes on an open
subscheme acquires paired locally finite Cartier-rank filtrations after an admissible
blowup away from that open subscheme. -/
theorem exists_afterAdmissibleBlowup {X : Scheme.{u}} (F : X.Modules)
    (U : X.Opens)
    (hPerfect : SheafOfModules.IsPerfect F)
    (hTor : RingedSpace.ModuleHasTorDimensionLE F 1)
    (hZero : IsZero (F.over U)) :
    ∃ (X' : Scheme.{u}) (b : X' ⟶ X)
      (G : CartierRankFiltrations ((Scheme.Modules.pullback b).obj F)),
      IsAdmissibleBlowup U b := sorry

end CartierRankFiltrations

end AlgebraicGeometry.Scheme.Modules
