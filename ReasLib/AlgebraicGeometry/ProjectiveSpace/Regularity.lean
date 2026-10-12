/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent

/-!
# Regularity on projective space

This file defines cohomological regularity using the canonical twists on standard projective
space.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- A coherent module sheaf `ℱ` on projective `n`-space is `m`-regular when the positive-degree
cohomology of every required canonical twist `ℱ(m - i)` vanishes. -/
abbrev IsMRegular
    (k : Type u) [Field k] (n : ℕ) (ℱ : (scheme k n).Modules) [ℱ.IsCoherent]
    (m : ℤ) : Prop :=
  ∀ i : ℕ, 0 < i → i ≤ n →
    IsZero
      (RingedSpace.moduleCohomology (X := (scheme k n).toRingedSpace)
        (twist k n ℱ (m - i)) i)

/-- A coherent module sheaf on projective space is regular exactly when its defining cohomological
vanishing condition. -/
theorem isMRegular_iff
    (k : Type u) [Field k] (n : ℕ) (ℱ : (scheme k n).Modules) [ℱ.IsCoherent]
    (m : ℤ) :
    IsMRegular k n ℱ m ↔
      ∀ i : ℕ, 0 < i → i ≤ n →
        IsZero
          (RingedSpace.moduleCohomology (X := (scheme k n).toRingedSpace)
            (twist k n ℱ (m - i)) i) := sorry

/-- An `m`-regular coherent module sheaf has vanishing cohomology in every required positive
degree. -/
theorem IsMRegular.isZero
    {k : Type u} [Field k] {n : ℕ} {ℱ : (scheme k n).Modules} [ℱ.IsCoherent] {m : ℤ}
    (hℱ : IsMRegular k n ℱ m) {i : ℕ} (hi : 0 < i) (hi_bound : i ≤ n) :
    IsZero
      (RingedSpace.moduleCohomology (X := (scheme k n).toRingedSpace)
        (twist k n ℱ (m - i)) i) := sorry

end AlgebraicGeometry.ProjectiveSpace
