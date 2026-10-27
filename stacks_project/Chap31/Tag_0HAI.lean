/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Rank.Generic
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.Scheme.Modules

universe u

/- Lemma (0HAI): On an integral scheme, generic cardinal rank is additive in a
short exact sequence of quasi-coherent modules. -/
@[stacks 0HAI] #check (AlgebraicGeometry.Scheme.Modules.genericRank_additive :
  ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
    (S : CategoryTheory.ShortComplex X.Modules)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent],
    S.ShortExact → genericRank S.X₂ = genericRank S.X₁ + genericRank S.X₃)
