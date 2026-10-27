/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Properties
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.AlphaP
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Smooth

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The relative Frobenius of a smooth morphism of fixed relative dimension in prime
characteristic is finite. -/
theorem relativeFrobenius_isFinite_of_smooth {p d : ℕ} [Fact p.Prime]
    {X S : Scheme.{u}} [Scheme.IsCharP S p] (f : X ⟶ S)
    [SmoothOfRelativeDimension d f] :
    IsFinite (relativeFrobenius (p := p) f) := by
  let hf : Smooth f := SmoothOfRelativeDimension.smooth d f
  let hfp : LocallyOfFinitePresentation f :=
    @AlgebraicGeometry.instLocallyOfFinitePresentationOfSmooth X S f hf
  let hft : LocallyOfFiniteType f :=
    @AlgebraicGeometry.instLocallyOfFiniteTypeOfLocallyOfFinitePresentation X S f hfp
  exact @relativeFrobenius_isFinite.{u} p ‹Fact p.Prime› X S f ‹Scheme.IsCharP S p› hft

/-- The relative Frobenius of a smooth morphism of fixed relative dimension in prime
characteristic is syntomic. -/
theorem relativeFrobenius_syntomic_of_smooth {p d : ℕ} [Fact p.Prime]
    {X S : Scheme.{u}} [Scheme.IsCharP S p] (f : X ⟶ S)
    [SmoothOfRelativeDimension d f] :
    Syntomic (relativeFrobenius (p := p) f) := sorry

set_option synthInstance.checkSynthOrder false in
/-- The relative Frobenius of a smooth morphism of relative dimension `d` in prime
characteristic is an iterated `α_p`-cover. -/
instance relativeFrobenius_isIteratedAlphaPCover {p d : ℕ} [Fact p.Prime]
    {X S : Scheme.{u}} [Scheme.IsCharP S p] [Scheme.IsCharP X p] (f : X ⟶ S)
    [SmoothOfRelativeDimension d f] :
    IsIteratedAlphaPCover p (relativeFrobenius (p := p) f) := sorry

set_option synthInstance.checkSynthOrder false in
/-- The relative Frobenius of a smooth morphism of relative dimension `d` in prime
characteristic is finite locally free of rank `p ^ d`. -/
instance relativeFrobenius_isFiniteLocallyFreeOfRank_of_smooth {p d : ℕ}
    [Fact p.Prime] {X S : Scheme.{u}} [Scheme.IsCharP S p] [Scheme.IsCharP X p]
    (f : X ⟶ S) [SmoothOfRelativeDimension d f] :
    IsFiniteLocallyFreeOfRank (relativeFrobenius (p := p) f) (p ^ d) := sorry

end AlgebraicGeometry.Scheme.Hom
