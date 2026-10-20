/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.FinitePresentation.Relative
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative finite presentation and products

Relative finite presentation passes from a binary product to either direct summand.

@stack 0672
-/

@[expose] public section

universe u v w x

namespace Module

variable {R : Type u} {A : Type v} {M : Type w} {M' : Type x}
variable [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
variable [AddCommGroup M] [Module A M]
variable [AddCommGroup M'] [Module A M']

/-- Lemma 15.81.10 (0672) (1): relative finite presentation of `M × M'` implies relative
finite presentation of the left summand. -/
@[stacks 0672 "left summand of a relatively finitely presented product"]
theorem finitePresentationRelativeTo_left_of_prod
    (h : Module.FinitePresentationRelativeTo R A (M × M')) :
    Module.FinitePresentationRelativeTo R A M := sorry
/- Proof strategy: test `h` on every polynomial presentation via
`iff_overEveryPolynomialPresentation`; after restricting scalars, apply
`Module.finitePresentation_of_split_exact` to the split sequence defined by `LinearMap.inl` and
`LinearMap.snd`. -/

/-- Lemma 15.81.10 (0672) (2): relative finite presentation of `M × M'` implies relative
finite presentation of the right summand. -/
@[stacks 0672 "right summand of a relatively finitely presented product"]
theorem finitePresentationRelativeTo_right_of_prod
    (h : Module.FinitePresentationRelativeTo R A (M × M')) :
    Module.FinitePresentationRelativeTo R A M' := sorry
/- Proof strategy: repeat the left-summand argument with the split sequence defined by
`LinearMap.inr` and `LinearMap.fst`, using `iff_overEveryPolynomialPresentation` to work over an
arbitrary polynomial presentation. -/

end Module
