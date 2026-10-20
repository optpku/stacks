/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist.Invertible
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.CanonicalAction
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Cohomology.AffineBase
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.FirstChern
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# Relative de Rham cohomology of standard projective space

This file records the iterated de Rham first-Chern powers of `𝒪(1)` on standard projective space
and the resulting rank-one even-degree cohomology with vanishing in complementary degrees.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- The iterated de Rham cup power of the first Chern class of `𝒪(1)` on standard
projective space. -/
noncomputable def deRhamChernPower
    (A : Type u) [CommRing A] (n : ℕ)
    (i : ℕ) :
    Scheme.DeRham.cohomologyOverAffineBase (toSpec A n) (2 * (i : ℤ)) :=
  by
    change Scheme.DeRham.cohomology (toSpec A n) (2 * (i : ℤ))
    exact Scheme.DeRham.CanonicalAction.evenPower (toSpec A n)
      (Scheme.DeRham.firstChernClass (toSpec A n) (twistingSheaf A n 1)) i

/-- For `i ≤ n`, the degree-`2 * i` relative de Rham cohomology of standard projective
`n`-space over `A` is free of rank one on the `i`th de Rham Chern power of `𝒪(1)`. -/
theorem deRhamChernPower_basis
    (A : Type u) [CommRing A] (n : ℕ) (hn : 1 ≤ n)
    (i : ℕ) (hi : i ≤ n) :
    ∃ b : Module.Basis (Fin 1) A
        (Scheme.DeRham.cohomologyOverAffineBase (toSpec A n) (2 * (i : ℤ))),
      b 0 = deRhamChernPower A n i := sorry

/-- The relative de Rham cohomology of standard projective `n`-space over `A` vanishes in
every integer degree outside `2 * i` for `i ≤ n`. -/
theorem deRhamCohomology_isZero
    (A : Type u) [CommRing A] (n : ℕ) (hn : 1 ≤ n) (q : ℤ)
    (hq : ¬ ∃ i : ℕ, i ≤ n ∧ q = 2 * (i : ℤ)) :
    IsZero (Scheme.DeRham.cohomologyOverAffineBase (toSpec A n) q) := sorry

end AlgebraicGeometry.ProjectiveSpace
