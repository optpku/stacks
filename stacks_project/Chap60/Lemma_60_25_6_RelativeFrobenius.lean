/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Smooth

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Hom

universe u

/- The canonical Frobenius twist preserves characteristic `p`. -/
#check (AlgebraicGeometry.Scheme.Hom.relativeFrobeniusTarget_isCharP :
  {p : ℕ} → [Fact p.Prime] → {X S : Scheme.{u}} → [Scheme.IsCharP S p] →
    (f : X ⟶ S) → Scheme.IsCharP (relativeFrobeniusTarget (p := p) f) p)

/- The smooth relative Frobenius has its canonical cover and degree properties. -/
#check (AlgebraicGeometry.Scheme.Hom.relativeFrobenius_isIteratedAlphaPCover :
  {p d : ℕ} → [Fact p.Prime] → {X S : Scheme.{u}} → [Scheme.IsCharP S p] →
    [Scheme.IsCharP X p] → (f : X ⟶ S) → [SmoothOfRelativeDimension d f] →
      IsIteratedAlphaPCover p (relativeFrobenius (p := p) f))

/- The smooth relative Frobenius has its canonical cover and degree properties. -/
#check (AlgebraicGeometry.Scheme.Hom.relativeFrobenius_isFiniteLocallyFreeOfRank_of_smooth :
  {p d : ℕ} → [Fact p.Prime] → {X S : Scheme.{u}} → [Scheme.IsCharP S p] →
    [Scheme.IsCharP X p] → (f : X ⟶ S) → [SmoothOfRelativeDimension d f] →
      IsFiniteLocallyFreeOfRank (relativeFrobenius (p := p) f) (p ^ d))

