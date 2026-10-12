/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.FiniteDescent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 33.38.14: let `f : X ⟶ Y` be a morphism of schemes. Assume `Y` is Noetherian of
dimension at most `1`, `f` is finite, and there exists a dense open `V ⊆ Y` such that the
restricted morphism `f ∣_ V : (f ⁻¹ᵁ V).toScheme ⟶ V` is a closed immersion. Then every
invertible `𝒪_X`-module is the pullback of an invertible `𝒪_Y`-module. -/
@[stacks 0C0U] #check
  (AlgebraicGeometry.Scheme.Hom.FiniteDescent.existsInvertiblePullback_of_exists_dense_open_isClosedImmersion :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
      [AlgebraicGeometry.IsNoetherian Y]
      (_ : topologicalKrullDim Y ≤ 1)
      (_ : ∃ V : Y.Opens, Dense (V : Set Y) ∧ IsClosedImmersion (f ∣_ V)),
      ∀ (L : X.Modules) [Scheme.Modules.Invertible L],
        ∃ (N : Y.Modules) (_ : Scheme.Modules.Invertible N),
          Nonempty (L ≅ (Scheme.Modules.pullback f).obj N))
