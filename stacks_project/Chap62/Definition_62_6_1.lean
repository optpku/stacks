/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RelativeCycle
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- Definition 62.6.1 (1): Let `S` be a locally Noetherian scheme. Let `f : X ⟶ S` be a
morphism of schemes which is locally of finite type. Let `r ≥ 0` be an integer. A
relative `r`-cycle on `X / S` is a family `α` of `r`-cycles on fibres of `X / S` such
that for every morphism `g : S' ⟶ S` where `S'` is the spectrum of a discrete
valuation ring we have `sp_{X'/S'}(α_η) = α_0`, where `sp_{X'/S'}` is specialization
of cycles over a DVR and `α_η` (resp. `α_0`) is the value of the base change `g^*α`
at the generic (resp. closed) point of `S'`. -/
@[stacks 0H50]
#check (AlgebraicGeometry.RelativeCycle.IsRelative :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S} [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] {r : ℕ}, f.FiberCycleFamily r → Prop)

/- Definition 62.6.1 (2): the group of all relative `r`-cycles on `X / S` is denoted
`z(X/S, r)`. -/
@[stacks 0H50]
#check (AlgebraicGeometry.RelativeCycle.group :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] (r : ℕ), AddSubgroup (f.FiberCycleFamily r))
