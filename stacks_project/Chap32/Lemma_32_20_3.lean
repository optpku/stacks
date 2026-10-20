module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Over.StalkGluing
import StacksCheckRecall

/-!
# Lemma 32.20.3

The finite-presentation neighborhood and stalk-gluing API is owned by
`ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Over.StalkGluing`.

@stack 0BQ5
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty
open AlgebraicGeometry

universe u

/- Lemma 32.20.3: Finite-presentation schemes over open neighborhoods of `s` containing `U`
have colimit equivalent to compatible finite-presentation schemes over `U` and
`Spec(𝒪_{S,s})`, identified over `Spec(𝒪_{S,s}) ×_S U`. -/
@[stacks 0BQ5] #check
  (AlgebraicGeometry.FinitePresentationOver.OpenNeighborhood.stalkGluingFunctor_isEquivalence :
    ∀ (S : Scheme.{u}) (U : S.Opens) [QuasiCompact U.ι]
      (s : S), s ∉ (U : Set S) →
      (AlgebraicGeometry.FinitePresentationOver.OpenNeighborhood.stalkGluingFunctor S U s).IsEquivalence)
