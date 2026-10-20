/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RelativeCycle.Thickening
import StacksCheckRecall

/-!
# Lemma 62.6.14

Pushforward of relative cycles along a thickening of schemes locally of finite
type over a locally Noetherian base.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.RelativeCycle

/- Lemma 62.6.14: if `S` is locally Noetherian and `i : X ⟶ X'` is a thickening
of schemes locally of finite type over `S`, then for every `r ≥ 0` the
pushforward `i_* : z(X/S, r) → z(X'/S, r)` is a bijection. -/
@[stacks 0H5E]
#check (AlgebraicGeometry.RelativeCycle.groupPushforward_bijective :
  ∀ {X X' S : Scheme.{u}} (fX : X ⟶ S)
    (fX' : X' ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType fX]
    [LocallyOfFiniteType fX'] (i : X ⟶ X') [IsThickening i]
    (hc : i ≫ fX' = fX) (r : ℕ),
    Function.Bijective (groupPushforward fX fX' i hc r))

end AlgebraicGeometry.RelativeCycle
