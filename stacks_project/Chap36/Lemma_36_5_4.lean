/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.Affine

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 36.5.4 (1): for an affine morphism `f : X ⟶ S`, derived direct image
induces an equivalence `D_QCoh(𝒪_X) ⟶ D_QCoh(f_*𝒪_X)`. -/
@[stacks 0AVW] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.affinePushforwardToPushforwardStructure.isEquivalence :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f],
      Functor.IsEquivalence (Scheme.DerivedQCoh.affinePushforwardToPushforwardStructure f))

/- Lemma 36.5.4 (2): composing this equivalence with restriction of scalars
`D_QCoh(f_*𝒪_X) ⟶ D_QCoh(𝒪_S)` recovers `Rf_*` up to natural isomorphism. -/
@[stacks 0AVW] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.affinePushforwardToPushforwardStructure.compRestriction_isomorphic :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f],
      IsIsomorphic
        (Scheme.DerivedQCoh.affinePushforwardToPushforwardStructure f ⋙
          Scheme.DerivedQCoh.pushforwardQCohRestriction f)
        (Scheme.DerivedQCoh.pushforwardCohomologyIn f))
