/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernCycle

/-! Canonical first Chern cap on the genuine rational quotient and its powers. -/
@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace.Hom
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernChow
variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (L : X.Modules) [isInvertibleObject L]

/-- First Chern intersection annihilates rationally trivial cycles. -/
theorem boundaries_le_ker (k : ℤ) :
    RationalEquivalence.boundaries f δ (k + 1) ≤ (firstChernClassCap f δ L k).ker := sorry

/-- First Chern intersection on Chow groups, induced from intersection on cycles. -/
def cap (k : ℤ) : Hom.chowGroup f δ (k + 1) →+ Hom.chowGroup f δ k :=
  QuotientAddGroup.lift (RationalEquivalence.boundaries f δ (k + 1))
    (firstChernClassCap f δ L k) (boundaries_le_ker f δ L k)

/-- First Chern intersection agrees with cycle intersection on every representative. -/
@[simp] theorem cap_mk (k : ℤ) (a : Hom.cycleGroup f δ (k + 1)) :
    cap f δ L k (Hom.chowMk f δ (k + 1) a) = firstChernClassCap f δ L k a := rfl

/-- Degree-indexed first Chern cap CH_k → CH_(k-1), with the actual arithmetic cast. -/
def lower (k : ℤ) : Hom.chowGroup f δ k →+ Hom.chowGroup f δ (k - 1) :=
  (cap f δ L (k - 1)).comp
    ((AddEquiv.cast (M := Hom.chowGroup f δ) (show k = (k - 1) + 1 by omega)).toAddMonoidHom)

/-- The iterated degree-lowering first Chern operation on Chow groups. -/
def power (n : ℕ) : ∀ k : ℤ, Hom.chowGroup f δ k →+ Hom.chowGroup f δ (k - n) :=
  Nat.rec
    (fun k ↦ (AddEquiv.cast (M := Hom.chowGroup f δ) (show k = k - (0 : ℕ) by omega)).toAddMonoidHom)
    (fun n prev k ↦
      ((AddEquiv.cast (M := Hom.chowGroup f δ) (show (k - n) - 1 = k - (n + 1 : ℕ) by omega)).toAddMonoidHom).comp
        ((lower f δ L (k - n)).comp (prev k))) n

/-- The zeroth iterate is additive transport along the zero degree shift. -/
@[simp] theorem power_zero (k : ℤ) :
    power f δ L 0 k = (AddEquiv.cast (M := Hom.chowGroup f δ) (show k = k - (0 : ℕ) by omega)).toAddMonoidHom := rfl

/-- The successor iterate applies one more degree-lowering first Chern operation. -/
theorem power_succ (n : ℕ) (k : ℤ) (a : Hom.chowGroup f δ k) :
    power f δ L (n + 1) k a =
      (AddEquiv.cast (M := Hom.chowGroup f δ) (show (k - n) - 1 = k - (n + 1 : ℕ) by omega)).toAddMonoidHom
        (lower f δ L (k - n) (power f δ L n k a)) := rfl

end AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernChow
