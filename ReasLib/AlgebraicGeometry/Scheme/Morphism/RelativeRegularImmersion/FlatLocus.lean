/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeRegularImmersion.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeRegularImmersion.FlatAt
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeRegularImmersion.FlatFinitePresentation

/-!
# Flat neighborhoods of relative H₁-regular immersions

A relative `H₁`-regular immersion over a locally finitely presented morphism has a flat open
neighborhood. It is regular, and remains regular after arbitrary base change.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RelativeH1RegularImmersion

variable {X S Z : Scheme.{u}} {f : X ⟶ S} {i : Z ⟶ X}

/-- A relative `H₁`-regular immersion over a locally finitely presented morphism factors through
an open subscheme on which the ambient morphism is flat. -/
theorem exists_flat_openFactorization_of_locallyOfFinitePresentation
    [RelativeH1RegularImmersion f i] [LocallyOfFinitePresentation f] :
    ∃ U : X.Opens, ∃ j : Z ⟶ U.toScheme, j ≫ U.ι = i ∧ Flat (U.ι ≫ f) := sorry

/-- A relative `H₁`-regular immersion over a locally finitely presented morphism is a regular
immersion. -/
theorem isRegularImmersion_of_locallyOfFinitePresentation
    [RelativeH1RegularImmersion f i] [LocallyOfFinitePresentation f] :
    IsRegularImmersion i := sorry

/-- Arbitrary base change of a relative `H₁`-regular immersion over a locally finitely presented
morphism is a regular immersion. -/
instance isRegularImmersion_pullback_snd_of_locallyOfFinitePresentation
    {S' : Scheme.{u}} [RelativeH1RegularImmersion f i] [LocallyOfFinitePresentation f]
    (g : S' ⟶ S) : IsRegularImmersion (pullback.snd i (pullback.fst f g)) := sorry

end AlgebraicGeometry.RelativeH1RegularImmersion
