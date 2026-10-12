/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_28_4_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
import StacksCheckRecall

@[expose] public section

/- Definition 67.28.1 (1): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` is
locally of finite presentation if the equivalent conditions of Lemma 67.22.1 hold with
`P` = locally of finite presentation. -/
@[stacks 03XP] #check AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation

/- Definition 67.28.1 (2): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` is
of finite presentation at a point `x` of `|X|` if some open neighbourhood `X' ⊂ X` of `x`
has locally of finite presentation restriction `f|_{X'} : X' ⟶ Y`. -/
@[stacks 03XP] #check AlgebraicGeometry.AlgebraicSpace.FinitePresentationAt

/- Definition 67.28.1 (3): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` is
of finite presentation if it is locally of finite presentation, quasi-compact, and
quasi-separated. -/
@[stacks 03XP] #check AlgebraicGeometry.AlgebraicSpace.FinitePresentation
