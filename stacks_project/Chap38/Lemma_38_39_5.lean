/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.DiscreteValuationRing
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 38.39.5: for a proper morphism with geometrically connected fibres over the
spectrum of a discrete valuation ring, freeness on the generic fibre and on one
uniformizer-power thickening detects global freeness of every finite locally free module. -/
@[stacks 0EXF] #check
  (AlgebraicGeometry.Scheme.Modules.exists_uniformizerPower_isFree_criterion :
    ∀ {R : CommRingCat.{u}} [IsDomain R] [IsDiscreteValuationRing R]
      (π : R) (_ : Irreducible π) {X : Scheme.{u}} (f : X ⟶ Spec R)
      [IsProper f] [GeometricallyConnected f],
      ∃ n : ℕ, ∀ (E : X.Modules) [E.IsFiniteLocallyFree],
        ((Scheme.Modules.pullback (f.fiberι (⊥ : PrimeSpectrum R))).obj E).IsFree →
          ((Scheme.Modules.pullback
            (pullback.fst f (Spec.quotientMap (Ideal.span {π ^ n})))).obj E).IsFree →
            E.IsFree)
