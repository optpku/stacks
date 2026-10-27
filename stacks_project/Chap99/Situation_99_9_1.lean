/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Hilbert.Functor

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

/- Situation 99.9.1: let `S` be a scheme and let `f : X ⟶ B` be a morphism of
finite presentation of algebraic spaces over `S`. For a scheme `T` over `B`,
write `X_T` for the base change of `X` to `T`. The Hilbert functor
`Hilb_{X/B} : (Sch/B)ᵒᵖ ⥤ Sets` associated to `X/B` sends `T` to the set of
closed subspaces `Z ⊂ X_T` such that `Z ⟶ T` is of finite presentation, flat,
and proper. Base change of closed immersions, finite presentation, flatness,
and properness yields a functor. -/
@[stacks 0CZY] #check (AlgebraicGeometry.AlgebraicSpace.Hilbert.hilbert :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f],
    (SchemeOver B)ᵒᵖ ⥤ Type (u + 1))
