/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Devissage
import StacksCheckRecall

open AlgebraicGeometry

universe u

/- Lemma 30.12.6: let `X` be a nonempty Noetherian scheme and let `P` be a property of
coherent `𝒪_X`-modules satisfying two-out-of-three for short exact sequences. If every
integral closed subscheme has a coherent generic-rank-one model with exact support satisfying
`P`, then `P` holds for every coherent module on `X`. -/
@[stacks 01YI] #check
  (AlgebraicGeometry.Scheme.Modules.devissagePropertyHoldsOfGenericRankOneSheaves :
    ∀ {X : Scheme.{u}} [Nonempty X] [IsNoetherian X]
      (P : X.Modules → Prop)
      (h_shortExact : AlgebraicGeometry.Scheme.Modules.DevissageTwoOutOfThree P)
      (h_generic :
        ∀ (Z : X.IdealSheafData) (h_integral : IsIntegral Z.subscheme)
          (ξ : X), IsGenericPoint ξ (Z.support : Set X) →
            ∃ 𝒢 : X.Modules,
              AlgebraicGeometry.Scheme.Modules.DevissageGenericRankOneSheaf Z ξ P 𝒢)
      (ℱ : X.Modules) [ℱ.IsCoherent],
      P ℱ)
