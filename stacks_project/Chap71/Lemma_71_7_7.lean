/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.ZeroSection.UniversalProperty
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.ZeroScheme
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Lemma 71.7.7 (1) and (2): a morphism pulls the section back to zero exactly when
it factors through the zero scheme. Together with vanishing on the zero-scheme
inclusion checked below, this gives maximality among vanishing closed subspaces. -/
@[stacks 0846]
#check (AlgebraicGeometry.AlgebraicSpace.pullbackSections_eq_zero_iff_exists_factorization_zeroScheme :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (L : X.Modules)
    [isInvertibleObject L] (s : L.sections) (f : Y ⟶ X),
    Modules.sectionsPullback f L s = 0 ↔
      ∃ g : Y ⟶ (zeroScheme L s).X, g ≫ zeroSchemeι L s = f)

/- Lemma 71.7.7 (1): the section vanishes on the zero scheme itself. -/
@[stacks 0846]
#check (AlgebraicGeometry.AlgebraicSpace.zeroSchemeι_pullbackSections_eq_zero :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (L : X.Modules)
    [isInvertibleObject L] (s : L.sections),
    Modules.sectionsPullback (zeroSchemeι L s) L s = 0)

/- Lemma 71.7.7 (3): the zero scheme of a section of an invertible sheaf is a locally
principal closed subspace. -/
@[stacks 0846]
#check (AlgebraicGeometry.AlgebraicSpace.zeroScheme_isLocallyPrincipalClosedSubspace :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (L : X.Modules)
    [isInvertibleObject L] (s : L.sections),
    IsLocallyPrincipal (zeroSchemeι L s))

/- Lemma 71.7.7 (4): the zero scheme is an effective Cartier divisor if and only if the
section is regular. -/
@[stacks 0846]
#check (AlgebraicGeometry.AlgebraicSpace.zeroScheme_isEffectiveCartierDivisor_iff_isRegularSection :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (L : X.Modules)
    [isInvertibleObject L] (s : L.sections),
    IsEffectiveCartierDivisor (zeroSchemeι L s) ↔ IsRegularSection L s)
