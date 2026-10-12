/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

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
  (AlgebraicGeometry.finitePresentation_openNeighborhood_colimit_equivalence_stalkGluing :
    ∀ (S : Scheme.{u}) (U : S.Opens) [QuasiCompact U.ι]
      (s : S), s ∉ (U : Set S) →
      Nonempty
        (AlgebraicGeometry.FinitePresentationOver.OpenNeighborhood.Colimit S U s ≌
          AlgebraicGeometry.finitePresentationStalkGluingCategory S U s))
