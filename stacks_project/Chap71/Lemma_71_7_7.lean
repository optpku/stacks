module

public import stacks_project.Chap71.Lemma_71_7_7_Divisor
public import stacks_project.Chap71.Lemma_71_7_7_UniversalProperty
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Lemma 71.7.7 (1): the zero scheme is maximal among closed immersions on which the
section vanishes. -/
@[stacks 0846]
#check (exists_factorization_zeroScheme_of_pullbackSections_eq_zero :
  ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} (L : X.Modules)
    [isInvertibleObject L] (s : L.sections) (i : Z ⟶ X) [IsClosedImmersion i],
    Modules.sectionsPullback i L s = 0 →
      ∃ g : Z ⟶ (zeroScheme L s).X, g ≫ zeroSchemeι L s = i)

/- Lemma 71.7.7 (2): pullback of the section along an arbitrary morphism of algebraic
spaces vanishes if and only if that morphism factors through the zero scheme. -/
@[stacks 0846]
#check (pullbackSections_eq_zero_iff_exists_factorization_zeroScheme :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (L : X.Modules)
    [isInvertibleObject L] (s : L.sections) (f : Y ⟶ X),
    Modules.sectionsPullback f L s = 0 ↔
      ∃ g : Y ⟶ (zeroScheme L s).X, g ≫ zeroSchemeι L s = f)

/- Lemma 71.7.7 (3): the zero scheme of a section of an invertible sheaf is a locally
principal closed subspace. -/
@[stacks 0846]
#check (zeroScheme_isLocallyPrincipalClosedSubspace :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (L : X.Modules)
    [isInvertibleObject L] (s : L.sections),
    IsLocallyPrincipalClosedSubspace (zeroSchemeι L s))

/- Lemma 71.7.7 (4): the zero scheme is an effective Cartier divisor if and only if the
section is regular. -/
@[stacks 0846]
#check (zeroScheme_isEffectiveCartierDivisor_iff_isRegularSection :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (L : X.Modules)
    [isInvertibleObject L] (s : L.sections),
    IsEffectiveCartierDivisor (zeroSchemeι L s) ↔ IsRegularSection L s)
