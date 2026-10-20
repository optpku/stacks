/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Finite
import StacksCheckRecall

@[expose] public section

universe u v

/- Exercise 111.7.4: if a finite module vanishes after localization at a
multiplicative subset, it vanishes after inverting one element of that subset. -/
@[stacks 076A] #check (LocalizedModule.exists_away_subsingleton :
    ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommMonoid M] [Module R M]
      [Module.Finite R M] (S : Submonoid R)
      (hM : Subsingleton (LocalizedModule S M)),
      ∃ f ∈ S, Subsingleton (LocalizedModule.Away f M))

#check (LocalizedModule.subsingleton_of_away_subsingleton :
    ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommMonoid M] [Module R M]
      (S : Submonoid R) {f : R} (hf : f ∈ S)
      (hfM : Subsingleton (LocalizedModule.Away f M)),
      Subsingleton (LocalizedModule S M))

#check (LocalizedModule.subsingleton_iff_exists_away_subsingleton :
    ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommMonoid M] [Module R M]
      [Module.Finite R M] (S : Submonoid R),
      Subsingleton (LocalizedModule S M) ↔
        ∃ f ∈ S, Subsingleton (LocalizedModule.Away f M))
