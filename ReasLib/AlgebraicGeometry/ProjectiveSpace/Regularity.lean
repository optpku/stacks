/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Regularity
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent

/-!
# Regularity on projective space

This file specializes `ProjTwistFamily.IsMRegular` to the canonical twists on standard
projective space, retaining the coherence hypothesis of Stacks, Definition 08A3. The theorem
`isMRegular_iff_presentation` compares it to any presentation with these same twists; no
universal twist-presentation data is needed for the definition.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- A coherent module sheaf `ℱ` on projective `n`-space is `m`-regular when the positive-degree
cohomology of every required canonical twist `ℱ(m - i)` vanishes. This is the specialization
of `ProjTwistFamily.IsMRegular` to `twistingSheaf k n`, with cohomological bound `n`. -/
abbrev IsMRegular
    (k : Type u) [Field k] (n : ℕ) (ℱ : (scheme k n).Modules) [ℱ.IsCoherent]
    (m : ℤ) : Prop :=
  ProjTwistFamily.IsMRegular (twistingSheaf k n) ℱ n m

/-- A presentation whose actual twists are the canonical projective-space twists gives the
same regularity predicate, with cohomological bound `n`. The twist identification is explicit:
an arbitrary twist presentation need not record the canonical twisting sheaves. -/
theorem isMRegular_iff_presentation
    (k : Type u) [Field k] (n : ℕ) (ℱ : (scheme k n).Modules) [ℱ.IsCoherent]
    (m : ℤ) (P : ProjTwistPresentation (grading k n))
    (hTwist : ∀ d : ℤ, P.actualTwist d = twistingSheaf k n d) :
    IsMRegular k n ℱ m ↔ P.IsMRegular ℱ n m := by
  change ProjTwistFamily.IsMRegular (twistingSheaf k n) ℱ n m ↔
    ProjTwistFamily.IsMRegular P.actualTwist ℱ n m
  rw [show P.actualTwist = twistingSheaf k n from funext hTwist]

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
