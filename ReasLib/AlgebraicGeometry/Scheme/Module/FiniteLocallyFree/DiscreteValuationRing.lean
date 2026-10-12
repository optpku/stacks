/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.Scheme.Spec.IdealSubobject

/-!
# Finite locally free modules over discrete valuation rings

This file gives a freeness criterion for finite locally free modules on proper schemes over
discrete valuation rings.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- For a proper morphism with geometrically connected fibres over the spectrum of a discrete
valuation ring, freeness on the generic fibre and on one uniformizer-power thickening detects
global freeness of every finite locally free module. -/
theorem exists_uniformizerPower_isFree_criterion
    {R : CommRingCat.{u}} [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π) {X : Scheme.{u}} (f : X ⟶ Spec R)
    [IsProper f] [GeometricallyConnected f] :
    ∃ n : ℕ, ∀ (E : X.Modules) [E.IsFiniteLocallyFree],
      ((Scheme.Modules.pullback (f.fiberι (⊥ : PrimeSpectrum R))).obj E).IsFree →
        ((Scheme.Modules.pullback
          (pullback.fst f (Spec.quotientMap (Ideal.span {π ^ n})))).obj E).IsFree →
          E.IsFree := sorry

end AlgebraicGeometry.Scheme.Modules
