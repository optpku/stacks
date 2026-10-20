/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Dual

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ChernClass.Theory

/- Lemma 42.43.3: The degree-`i` Chern class of the dual of a finite locally free
module `E` is `(-1) ^ i` times the degree-`i` Chern class of `E`. -/
@[stacks 0FA5] #check
  (AlgebraicGeometry.ChernClass.Theory.component_dual :
    ∀ {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
      [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
      (classes : Theory δ p) (E : X.Modules) [E.IsFiniteLocallyFree] (i : ℕ),
      classes.component (Scheme.Modules.dual E) i =
        ((-1 : ℤ) ^ i) • classes.component E i)

end AlgebraicGeometry.ChernClass.Theory
