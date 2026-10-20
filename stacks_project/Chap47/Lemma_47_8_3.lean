/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.DerivedTorsion.Vanishing
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 47.8.3: if `I` is a finitely generated ideal and some `f ∈ I` acts by an
isomorphism on a derived `A`-module `K`, then its derived `I`-power-torsion object
`RΓ_I(K)` is zero. -/
@[stacks 0A6M]
#check (CategoryTheory.ModuleCat.IdealPowerTorsion.isZero_of_isIso_smul :
  ∀ {A : Type u} [CommRing A] (I : Ideal A), I.FG →
    ∀ {f : A}, f ∈ I → ∀ (K : DerivedCategory (ModuleCat A))
      [IsIso (f • 𝟙 K)],
      IsZero ((CategoryTheory.ModuleCat.IdealPowerTorsion.derivedTorsion I).obj K))
