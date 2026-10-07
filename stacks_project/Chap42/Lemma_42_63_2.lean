module

public import stacks_project.Chap42.Lemma_42_63_2_Comparison
import StacksCheckRecall

/-
Lemma 42.63.2: for a scheme `X` locally of finite type over a locally Dedekind
scheme `S`, capping with `[S]₁` canonically identifies degree-`p` bivariant
classes for `X ⟶ S` with `CH_(1 - p)(X)`.
-/
@[stacks 0FC5] #check @AlgebraicGeometry.BivariantClass.Dedekind.chowEquiv
