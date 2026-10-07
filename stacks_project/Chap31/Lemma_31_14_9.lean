module

import ReasLib.AlgebraicGeometry.Scheme.Divisor.ZeroScheme
import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroScheme.UniversalProperty
import StacksCheckRecall

open CategoryTheory

universe u

variable {X Y Z : AlgebraicGeometry.Scheme.{u}}

/- Lemma 31.14.9 (1): the zero scheme is maximal among closed subschemes on which the section
vanishes. -/
@[stacks 02OR]
#check (AlgebraicGeometry.Scheme.exists_factorization_zeroScheme_of_pullbackSections_eq_zero :
  ∀ (ℒ : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible ℒ]
      (s : ℒ.sections) (i : Z ⟶ X),
    AlgebraicGeometry.Scheme.Modules.sectionsPullback i ℒ s =
        (0 : ((AlgebraicGeometry.Scheme.Modules.pullback i).obj ℒ).sections) →
      ∃ g : Z ⟶ AlgebraicGeometry.Scheme.zeroScheme ℒ s,
        g ≫ AlgebraicGeometry.Scheme.zeroSchemeι ℒ s = i)

/- Lemma 31.14.9 (2): pullback of the section along an arbitrary scheme morphism vanishes if
and only if that morphism factors through the zero scheme. -/
@[stacks 02OR]
#check (AlgebraicGeometry.Scheme.pullbackSections_eq_zero_iff_exists_factorization_zeroScheme :
  ∀ (ℒ : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible ℒ]
      (s : ℒ.sections) (f : Y ⟶ X),
    AlgebraicGeometry.Scheme.Modules.sectionsPullback f ℒ s =
        (0 : ((AlgebraicGeometry.Scheme.Modules.pullback f).obj ℒ).sections) ↔
      ∃ g : Y ⟶ AlgebraicGeometry.Scheme.zeroScheme ℒ s,
        g ≫ AlgebraicGeometry.Scheme.zeroSchemeι ℒ s = f)

/- Lemma 31.14.9 (3): the zero scheme of a section of an invertible sheaf is a locally
principal closed subscheme. -/
@[stacks 02OR]
#check (AlgebraicGeometry.Scheme.zeroScheme_isLocallyPrincipalClosedSubscheme :
  ∀ (ℒ : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible ℒ]
      (s : ℒ.sections),
    AlgebraicGeometry.IsLocallyPrincipalClosedSubscheme
      (AlgebraicGeometry.Scheme.zeroSchemeι ℒ s))

/- Lemma 31.14.9 (4): the zero scheme is an effective Cartier divisor if and only if the
section is regular. -/
@[stacks 02OR]
#check (AlgebraicGeometry.Scheme.zeroScheme_isEffectiveCartierDivisor_iff_isRegularSection :
  ∀ (ℒ : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible ℒ]
      (s : ℒ.sections),
    AlgebraicGeometry.IsEffectiveCartierDivisor
        (AlgebraicGeometry.Scheme.zeroSchemeι ℒ s) ↔
      AlgebraicGeometry.RingedSpace.IsRegularSection ℒ s)
