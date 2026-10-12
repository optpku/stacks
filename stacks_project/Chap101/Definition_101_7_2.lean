/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact
import StacksCheckRecall

@[expose] public section

/- Definition 101.7.2: a morphism `f : X ⟶ Y` of algebraic stacks is
quasi-compact if for every quasi-compact algebraic stack `Z` and morphism
`Z ⟶ Y`, the fibre product `Z ×_Y X` is a quasi-compact algebraic stack.

Stacks writes `Z ×_Y X`; the Lean test uses a `PseudoPullbackCone f g` with
`fst : P ⟶ X` and `snd : P ⟶ Z`. -/
@[stacks 050U] #check AlgebraicGeometry.AlgebraicStack.QuasiCompact
