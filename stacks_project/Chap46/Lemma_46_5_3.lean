/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.AffineEquivalence
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace SheafOfModules

/- Lemma 46.5.3 -/
@[stacks 06ZJ] #check (SheafOfModules.affineEvaluationAdequateIsEquivalence :
  ∀ (τ : StandardTopology) (A : CommRingCat.{u}),
    (SheafOfModules.affineEvaluationAdequate τ A).IsEquivalence)

end SheafOfModules
