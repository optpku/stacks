/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.FiberCriterion

/-!
# Criterion of flatness by fibres over a Noetherian base

On locally Noetherian algebraic spaces, relative flatness of a coherent module over `Z`
together with fibrewise relative flatness over `Y` is equivalent, at points of the support,
to flatness of `Y` over `Z` together with relative flatness over `Y`.
-/

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Theorem 76.24.1: Let `S` be a scheme. Let `f : X ⟶ Y` and `Y ⟶ Z` be morphisms of
algebraic spaces over `S`. Let `F` be a quasi-coherent `𝒪_X`-module. Assume `X`, `Y`, `Z`
locally Noetherian, and `F` a coherent `𝒪_X`-module. Let `x ∈ |X|` with images
`y = Points.map f x` and `z = Points.map (f ≫ h) x`. If `x ∈ moduleSupport F`
(equivalently `¬ IsZero (stalkModuleCat xbar F)` whenever `xbar.image = x`), then `F` is
flat over `Z` at `x` and the restriction of `F` to its fibre over `z` is flat at `x` over
the fibre of `Y` over `z` if and only if `Y` is flat over `Z` at `y` and `F` is flat over
`Y` at `x`. -/
@[stacks 0APR] #check (AlgebraicGeometry.AlgebraicSpace.Modules.flatOverAt_and_fiber_iff :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (h : Y ⟶ Z) [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian Z] (F : X.Modules) [F.IsQuasicoherent] [F.IsCoherent]
    (x : Points X) (h_stalk : x ∈ moduleSupport F),
    (flatOverAt F (f ≫ h) x ∧ flatOnFiberAt_field F f h x) ↔
      (FlatAt h (Points.map f x) ∧ flatOverAt F f x))
