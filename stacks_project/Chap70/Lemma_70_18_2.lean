module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePresentation.Over.StalkGluing
import StacksCheckRecall

universe u

/- Lemma 70.18.2: let `S` be a scheme. Let `s ∈ S` be a closed point such that
`U = S \ {s} → S` is quasi-compact. With `V = Spec(𝒪_{S,s}) \ {s}` there is an
equivalence of categories `FP_S ⥤ FP_U ×_{FP_V} FP_{Spec(𝒪_{S,s})}`, where
`FP_T` is the category of algebraic spaces of finite presentation over `T`.
Here `V` is `(S.fromSpecStalk s) ⁻¹ᵁ U` when `U = S \ {s}`, and the functor is
`AlgebraicGeometry.AlgebraicSpace.FinitePresentationOver.stalkGlueFunctor U s`. -/
@[stacks 0E90] #check
  (AlgebraicGeometry.AlgebraicSpace.FinitePresentationOver.stalkGlueFunctor_isEquivalence :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (U : S.Opens)
      [AlgebraicGeometry.QuasiCompact U.ι] (s : S),
      s ∈ closedPoints S → (U : Set S) = ({s} : Set S)ᶜ →
      (AlgebraicGeometry.AlgebraicSpace.FinitePresentationOver.stalkGlueFunctor U s).IsEquivalence)
