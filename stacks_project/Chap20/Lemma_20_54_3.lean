/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.ProjectionFormula
import StacksCheckRecall

@[expose] public section

/-!
# Projection formula for perfect complexes

The reusable statement and its categorical infrastructure live in `ReasLib`; this chapter file
records the source label without rebuilding the opens-ringed-site presentation.
-/

/- Lemma 20.54.3: for a morphism of ringed spaces `f : X ⟶ Y`, a perfect object
`K ∈ D(𝒪_Y)`, and `E ∈ D(𝒪_X)`, the canonical projection-formula morphism
`R(f)_* E ⊗ᴸ K ⟶ R(f)_* (E ⊗ᴸ L(f)^* K)` is an isomorphism. -/
@[stacks 0B54]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect.isIso_leftMate
