/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.FiniteType.Localization
import StacksCheckRecall

@[expose] public section

universe u v

/- Exercise 111.56.3: if `algebraMap A B` is of finite type and the induced map
`algebraMap (Localization S) (Localization (Algebra.algebraMapSubmonoid B S))`
from `S⁻¹A` to `S⁻¹B` is surjective, then some `f ∈ S` makes
`Localization.awayMap (algebraMap A B) f : A_f → B_f` surjective. -/
@[stacks 09TY] #check
  (Algebra.FiniteType.exists_awayMap_surjective :
    ∀ {A : Type u} {B : Type v}
      [CommRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
      (S : Submonoid A),
      Function.Surjective
        (algebraMap (Localization S) (Localization (Algebra.algebraMapSubmonoid B S))) →
      ∃ f : S, Function.Surjective (Localization.awayMap (algebraMap A B) (f : A)))
