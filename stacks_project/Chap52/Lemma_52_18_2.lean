/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Distance.FiniteType
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 52.18.2: distance depends only on the closed support. -/
@[stacks 0EIZ] #check (AlgebraicGeometry.Scheme.distanceTo_preimage_le :
    ∀ {Y Y' : Scheme.{u}} [IsNoetherian Y] [UniversallyCatenary Y],
      (Z : Closeds Y) → (f : Y' ⟶ Y) → [Hom.FiniteType f] → (e : ℕ) →
        (∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (e : WithBot ℕ∞)) → (y' : Y') →
          Y.distanceTo Z (f y') ≤ f.distanceToPreimage Z y' + e - f.residueFieldTrdegAt y')

end AlgebraicGeometry.Scheme
