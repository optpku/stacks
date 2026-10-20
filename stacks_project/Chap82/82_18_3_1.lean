/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.ZeroCycle.Components
import StacksCheckRecall

/-!
# Equality of zero-section cycles with component sums on algebraic spaces

The equality `[Z(s)]_k = ∑ n_i [Z(s_i)]_k` is an equality of concrete cycles
in the setting of Situation 82.2.1.
-/

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- 82.18.3.1: In Situation 82.2.1 let `Y / B` be good, let `ℒ` be an invertible
`𝒪_Y`-module, and let `s` be a regular section with `dim_δ(Y) ≤ k + 1`.
Writing `[Y]_{k+1} = ∑ n_i [Y_i]` over the reduced irreducible components of
`δ`-dimension `k + 1`, and restricting `s` to sections `s_i` on them, one has
`[Z(s)]_k = ∑ n_i [Z(s_i)]_k` as `k`-cycles on `Y`. -/
@[stacks 0EQM]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.relativeZeroCycle_eq_sum_components :
  ∀ {S : Scheme.{u}} {B Y : AlgebraicSpace S} [UniversallyCatenary B]
    (p : Y ⟶ B) [QuasiSeparated p] [LocallyOfFiniteType p]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (ℒ : Y.Modules) [isInvertibleObject ℒ] (s : ℒ.sections)
    [IsRegularSection ℒ s] (k : ℤ),
    (∀ y : Points Y, Hom.relativeDimensionFunction p δ y ≤ k + 1) →
    relativeZeroCycle p δ ℒ s k = relativeZeroCycleComponentSum p δ ℒ s k)
