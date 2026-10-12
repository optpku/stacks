/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_38_1_GUnramified
public import stacks_project.Chap67.Lemma_67_38_5_Unramified
public import stacks_project.Chap67.Lemma_67_38_8_Unramified
import StacksCheckRecall

@[expose] public section

/- Definition 67.38.1 (1): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
is unramified if the equivalent conditions of Lemma 67.22.1 hold with `P` = unramified. -/
@[stacks 03ZH] #check AlgebraicGeometry.AlgebraicSpace.Unramified

/- Definition 67.38.1 (2): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
is unramified at a point `x` of `|X|` if some open neighbourhood `X' ⊂ X` of `x` has
unramified restriction `f|_{X'} : X' ⟶ Y`. -/
@[stacks 03ZH] #check AlgebraicGeometry.AlgebraicSpace.UnramifiedAt

/- Definition 67.38.1 (3): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
is G-unramified if the equivalent conditions of Lemma 67.22.1 hold with `P` = G-unramified. -/
@[stacks 03ZH] #check AlgebraicGeometry.AlgebraicSpace.GUnramified

/- Definition 67.38.1 (4): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
is G-unramified at a point `x` of `|X|` if some open neighbourhood `X' ⊂ X` of `x` has
G-unramified restriction `f|_{X'} : X' ⟶ Y`. -/
@[stacks 03ZH] #check AlgebraicGeometry.AlgebraicSpace.GUnramifiedAt
