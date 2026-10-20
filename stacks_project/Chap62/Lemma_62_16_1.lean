/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RelativeCycle.Approximation
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open Scheme.Hom

universe u

/- Lemma 62.16.1: for a quasi-compact quasi-separated scheme `S`, a morphism
`f : X ⟶ S` of finite presentation, `r ≥ 0`, and a family `α` of `r`-cycles on
fibres of `X / S`, the following are equivalent: (1) `α` is the base change of
some relative `r`-cycle `α0 ∈ z(X0 / S0, r)` along a cartesian square from a
finite type morphism of Noetherian schemes `X0 ⟶ S0`; (2) some completely
decomposed proper morphism `g : S' ⟶ S` of finite presentation has `g^* α` in
the image of the Hilbert cycle-class map `hilbertCycleClass` (62.16.0.1). -/
@[stacks 0H6W] #check
  (AlgebraicGeometry.RelativeCycle.existsNoetherianBaseChange_iff_existsCompletelyDecomposedHilbert :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [CompactSpace S] [QuasiSeparatedSpace S] [Scheme.Hom.FinitePresentation f]
      (r : ℕ) (α : f.FiberCycleFamily (r : ℤ)),
      AlgebraicGeometry.RelativeCycle.existsNoetherianBaseChange f r α ↔
        AlgebraicGeometry.RelativeCycle.existsCompletelyDecomposedHilbert f r α)
