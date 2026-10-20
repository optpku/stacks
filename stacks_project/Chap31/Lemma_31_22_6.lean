module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeRegularImmersion.FlatLocus
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 31.22.6 (1): a relative `H₁`-regular immersion over a locally finitely presented
morphism factors through an open subscheme on which the ambient morphism is flat. -/
@[stacks 063V] #check
  (AlgebraicGeometry.RelativeH1RegularImmersion.exists_flat_openFactorization_of_locallyOfFinitePresentation :
    ∀ {X S Z : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S} {i : Z ⟶ X}
      [AlgebraicGeometry.RelativeH1RegularImmersion f i]
      [AlgebraicGeometry.LocallyOfFinitePresentation f],
      ∃ U : X.Opens, ∃ j : Z ⟶ U.toScheme,
        j ≫ U.ι = i ∧ AlgebraicGeometry.Flat (U.ι ≫ f))

/- Lemma 31.22.6 (2): a relative `H₁`-regular immersion over a locally finitely presented
morphism is a regular immersion. -/
@[stacks 063V] #check
  (AlgebraicGeometry.RelativeH1RegularImmersion.isRegularImmersion_of_locallyOfFinitePresentation :
    ∀ {X S Z : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S} {i : Z ⟶ X}
      [AlgebraicGeometry.RelativeH1RegularImmersion f i]
      [AlgebraicGeometry.LocallyOfFinitePresentation f],
      AlgebraicGeometry.IsRegularImmersion i)

/- Lemma 31.22.6 (3): arbitrary base change of a relative `H₁`-regular immersion over a locally
finitely presented morphism is a regular immersion. -/
@[stacks 063V] #check
  (AlgebraicGeometry.RelativeH1RegularImmersion.isRegularImmersion_pullback_snd_of_locallyOfFinitePresentation :
    ∀ {X S S' Z : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S} {i : Z ⟶ X}
      [AlgebraicGeometry.RelativeH1RegularImmersion f i]
      [AlgebraicGeometry.LocallyOfFinitePresentation f] (g : S' ⟶ S),
      AlgebraicGeometry.IsRegularImmersion
        (CategoryTheory.Limits.pullback.snd i (CategoryTheory.Limits.pullback.fst f g)))
