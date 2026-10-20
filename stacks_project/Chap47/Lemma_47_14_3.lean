/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension.BaseChange.InternalHom.Perfect

@[expose] public section

noncomputable section

open CategoryTheory
open DerivedCategory

universe u

/- Lemma 47.14.3: if `A` is perfect over `R` and `A` and `R'` are Tor independent
over `R`, then the trivial-duality base-change map is an isomorphism for every `K` in `D(R)`. -/
@[stacks 0BZP] #check
  (CategoryTheory.ModuleCat.trivialDualityBaseChangeMap_isIso_of_isPerfect :
    ∀ {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
      [Algebra R A] [Algebra R R']
      (K : DerivedCategory (ModuleCat.{u} R))
      (hA : (ModuleCat.of R A).IsPerfect)
      (hTor : CategoryTheory.ModuleCat.Tor.IsIndependent
        (ModuleCat.of R A) (ModuleCat.of R R')),
      IsIso (CategoryTheory.ModuleCat.trivialDualityBaseChangeMap K hTor))
