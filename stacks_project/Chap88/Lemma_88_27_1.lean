module

public import stacks_project.Chap88.«88_27_0_1»
public import stacks_project.Chap88.Lemma_88_27_1_BaseChange
public import stacks_project.Chap88.Lemma_88_27_1_Comparison

/-!
# Functoriality of the completion functor

The square of categories `Source X T ⟶ Target X T` over
`Source X1 T1 ⟶ Target X1 T1` 2-commutes, with horizontals the completion
functor and verticals base change along `X1 ⟶ X` and along `map h T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace completionAlong

/-- Lemma 88.27.1: in the situation of `completionFunctor`, let `h : X1 ⟶ X` be a
morphism of algebraic spaces with `X1` locally Noetherian, and write `T1` for
the inverse image of `T` on `X1`. The square of categories
`Source X T ⟶ Target X T` over `Source X1 T1 ⟶ Target X1 T1` 2-commutes:
horizontals are `functor`/`completionFunctor`, and verticals are
`sourceBaseChange h T` and `targetBaseChange h T` given by base change along
`h` and along `map h T`. Equivalently, the comparison 2-cell
`baseChangeHom h T` is an isomorphism. -/
@[stacks 0GDQ]
instance instIsIso_baseChangeHom {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) : IsIso (baseChangeHom h T) :=
  sorry

end completionAlong

end AlgebraicGeometry.AlgebraicSpace
