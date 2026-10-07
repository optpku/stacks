module

import ReasLib.AlgebraicGeometry.Scheme.Module.FittingIdeal.CartierFiltration
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped ModuleRestriction ZeroObject

universe u

/- Lemma 38.41.3: a perfect scheme module of Tor dimension at most one which
vanishes on `U` acquires paired locally finite Cartier-rank filtrations after a
`U`-admissible blowup. -/
@[stacks 0ESU] #check
  (AlgebraicGeometry.Scheme.Modules.CartierRankFiltrations.exists_afterAdmissibleBlowup :
    ∀ {X : Scheme.{u}} (F : X.Modules) (U : X.Opens),
      SheafOfModules.IsPerfect F →
      RingedSpace.ModuleHasTorDimensionLE F 1 →
      IsZero (F.over U) →
      ∃ (X' : Scheme.{u}) (b : X' ⟶ X)
        (G : Scheme.Modules.CartierRankFiltrations ((Scheme.Modules.pullback b).obj F)),
        IsAdmissibleBlowup U b)
