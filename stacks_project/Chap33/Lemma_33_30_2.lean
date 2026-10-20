/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.AffineBaseChange

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

universe u

/- Lemma 33.30.2: for a faithfully flat ring map `A → B` and a quasi-compact,
quasi-separated `A`-scheme `X` with semilocal global-sections ring, pullback
`Pic(X) → Pic(X_B)` is injective. -/
@[stacks 0CDY] #check
  (AlgebraicGeometry.Scheme.AffineBaseChange.picardPullback_injective :
    ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
      [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]
      [Finite (MaximalSpectrum (Γ(X, ⊤)))],
      (algebraMap A B).FaithfullyFlat →
        Function.Injective
          (Scheme.Hom.picardPullback (Scheme.AffineBaseChange.toSource A B f)))
