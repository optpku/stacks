/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Relative
public import stacks_project.Chap60.Lemma_60_25_4_AlphaP

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The Frobenius twist of a morphism to a scheme of characteristic `p` again has
characteristic `p`. -/
instance relativeFrobeniusTarget_isCharP {p : ℕ} [Fact p.Prime]
    {X S : Scheme.{u}} [Scheme.IsCharP S p] (f : X ⟶ S) :
    Scheme.IsCharP (relativeFrobeniusTarget (p := p) f) p :=
  sorry

set_option synthInstance.checkSynthOrder false in
/-- The relative Frobenius of a smooth morphism of relative dimension `d` in prime
characteristic is an iterated `α_p`-cover. -/
instance relativeFrobenius_isIteratedAlphaPCover {p d : ℕ} [Fact p.Prime]
    {X S : Scheme.{u}} [Scheme.IsCharP S p] [Scheme.IsCharP X p] (f : X ⟶ S)
    [SmoothOfRelativeDimension d f] :
    IsIteratedAlphaPCover p (relativeFrobenius (p := p) f) :=
  sorry

set_option synthInstance.checkSynthOrder false in
/-- The relative Frobenius of a smooth morphism of relative dimension `d` in prime
characteristic is finite locally free of rank `p ^ d`. -/
instance relativeFrobenius_isFiniteLocallyFreeOfRank_of_smooth {p d : ℕ}
    [Fact p.Prime] {X S : Scheme.{u}} [Scheme.IsCharP S p] [Scheme.IsCharP X p]
    (f : X ⟶ S) [SmoothOfRelativeDimension d f] :
    IsFiniteLocallyFreeOfRank (relativeFrobenius (p := p) f) (p ^ d) :=
  sorry

end AlgebraicGeometry.Scheme.Hom
