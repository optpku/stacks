/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Duality
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tor-amplitude of the perfect derived dual

@stack 0H81
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.DerivedCategory.InternalHom
open CategoryTheory.MonoidalCategory

namespace CategoryTheory.DerivedCategory.Perfect.Duality

variable {A : Type u} [CommRing A]
variable [MonoidalCategory (DerivedCategory (ModuleCat A))]
variable [BraidedCategory (DerivedCategory (ModuleCat A))]
variable [RHom.Has (A := A)]
variable [DerivedTensor.Right.Has (C := ModuleCat A)]

/-- Remark 15.75.16 (0H81): the dual of a perfect object with Tor-amplitude `[a, b]` has
Tor-amplitude `[-b, -a]`. -/
@[stacks 0H81 "Tor-amplitude of the perfect derived dual"]
theorem dual_hasTorAmplitudeIn_neg_swap
    (M : RHom.ClosedComparison (A := A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat A)))
    {K : DerivedCategory (ModuleCat A)} {a b : ℤ}
    (hK : K.IsPerfect)
    (hamp : HasTorAmplitudeIn (R := A) K a b) :
    HasTorAmplitudeIn (R := A) (selectedDual M K) (-b) (-a) := sorry
/- Proof strategy: choose the strictly perfect representative supplied by `hK`, identify
`selectedDual M K` through perfect duality with its termwise dual, and use `hamp` to place that
dual representative in the reversed support interval `[-b, -a]`. -/

end CategoryTheory.DerivedCategory.Perfect.Duality

end
