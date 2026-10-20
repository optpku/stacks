/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap89.Definition_89_4_1_PointBlowup
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

/- Definition 89.4.1: Let `S` be a scheme. Let `X` be a decent algebraic space over `S`.
Let `x ∈ |X|` be a closed point. By Decent Spaces, Lemma 68.14.6 we can represent `x`
by a closed immersion `i : Spec(k) ⟶ X`. The blowing up `X' ⟶ X` of `X` at `x` means
the blowing up of `X` in the closed subspace `Z = i(Spec(k)) ⊂ X`. -/
@[stacks 0BHE] #check Blowup.atPoint
#check ClosedSubspace.ofClosedPoint
