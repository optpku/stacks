/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.PresheafPullback
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u a b

variable {S : Scheme.{u}} {X : GroupoidsOver S} {A : Type a} [Category.{b} A]

/- Definition 96.9.2 (1): let `p : X ⟶ (Sch/S)_fppf` be a category fibred in
groupoids, let `x` lie over `U = p(x)`, and let `F` be a presheaf on `X`.
The pullback `x⁻¹ F` is the restriction of `F` to `X/x`, viewed as a
presheaf on `(Sch/U)_fppf` via the equivalence `X/x ⟶ (Sch/U)_fppf` of
Lemma 96.9.1. The 2-Yoneda 1-morphism of `x` is the chosen quasi-inverse. -/
@[stacks 06W1]
#check (AlgebraicGeometry.GroupoidsOver.pullbackPresheaf :
  (x : X.total) → (X.totalᵒᵖ ⥤ A) → (Over (X.p.obj x).left)ᵒᵖ ⥤ A)

/- Definition 96.9.2 (2): the restriction of `F` to `U_étale` is
`(x⁻¹ F)|_{U_étale}`, abusively written `F|_{U_étale}`. -/
@[stacks 06W1]
#check (AlgebraicGeometry.GroupoidsOver.restrictSmallEtale :
  (x : X.total) → (X.totalᵒᵖ ⥤ A) → (X.p.obj x).left.Etaleᵒᵖ ⥤ A)
