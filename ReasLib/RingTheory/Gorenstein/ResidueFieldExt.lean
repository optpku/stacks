/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Gorenstein.Local
public import ReasLib.Algebra.Homology.DerivedCategory.InjectiveAmplitude.Local
public import ReasLib.CategoryTheory.DerivedCategory.InjectiveAmplitude.Single

@[expose] public section

universe u

open CategoryTheory
open scoped DerivedExt

namespace IsGorensteinLocalRing

/-- A Noetherian local commutative ring is Gorenstein exactly when the derived Ext groups
from its residue field to the ring are subsingleton in all sufficiently large degrees. -/
theorem iff_eventually_residueField_ext
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    IsGorensteinLocalRing A ↔
      ∃ b : ℤ, ∀ i : ℤ, b < i →
        Subsingleton
          (Ext⁽i⁾((DerivedCategory.singleFunctor (ModuleCat A) 0).obj
            (ModuleCat.of A (IsLocalRing.ResidueField A)),
            (DerivedCategory.singleFunctor (ModuleCat A) 0).obj (ModuleCat.of A A))) := sorry

end IsGorensteinLocalRing
