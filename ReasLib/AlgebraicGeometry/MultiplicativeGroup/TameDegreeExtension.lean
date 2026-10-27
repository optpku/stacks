/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.MultiplicativeGroup.TameLabels
public import ReasLib.Topology.Algebra.Category.ProfiniteGrp.DegreeExtension
public import ReasLib.NumberTheory.Padics.PrimeTo.Basic

/-! The tame fundamental-group degree extension of the multiplicative group over a prime field. -/

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme TopologicalSpace
noncomputable section

namespace MultiplicativeGroupTame
variable (p : ℕ) [Fact p.Prime]

/-- The geometric generic point of the multiplicative group over the prime field. -/
abbrev sourcePoint := genericPoint (ZMod p)

/-- The degree map at the geometric generic point is surjective onto the profinite integers. -/
theorem sourceDegree_surjective : Function.Surjective (degreeToIntegers p (sourcePoint p)) :=
  degreeToIntegers_surjective p (sourcePoint p)

/-- The degree extension of the tame fundamental group at the geometric generic point. -/
def sourceExtension : ProfiniteGrp.DegreeExtension.{1} where
  middle := fundamentalGroup (ZMod p) (sourcePoint p)
  deg := degreeToIntegers p (sourcePoint p)
  deg_surjective := sourceDegree_surjective p

/-- The middle group of the tame degree extension is the tame fundamental group. -/
theorem sourceExtension_middle : (sourceExtension p).middle =
    fundamentalGroup (ZMod p) (sourcePoint p) := rfl

/-- The degree homomorphism of the tame degree extension is the arithmetic degree map. -/
theorem sourceExtension_degree : (sourceExtension p).deg =
    degreeToIntegers p (sourcePoint p) := rfl

/-- The closed kernel of the tame degree extension is the geometric tame kernel. -/
theorem sourceExtension_kernel : (sourceExtension p).kerClosed =
    geometricKernel p (sourcePoint p) := rfl

/-- The closed points of a specified positive degree on the multiplicative group over the prime field. -/
abbrev sourcePoints (d : ℕ+) := points (ZMod p) d

/-- Quotient labels match the already constructed orbit on every actual representative. -/
def LabelsMatchOrbit
    (F : ∀ d : ℕ+, sourcePoints p d → ConjClasses (sourceExtension p).middle) : Prop :=
  ∀ (d : ℕ+) (x : sourcePoints p d) (g : (sourceExtension p).middle),
    g ∈ (labels (ZMod p) (sourcePoint p) d x).carrier ↔ ConjClasses.mk g = F d x

/-- Closed points have quotient Frobenius labels matching their conjugacy orbits and degrees. -/
theorem exists_source_labels :
    ∃ F : ∀ d : ℕ+, sourcePoints p d → ConjClasses (sourceExtension p).middle,
      LabelsMatchOrbit p F ∧
      ∀ (d : ℕ+) (x : sourcePoints p d),
        (sourceExtension p).degClass (F d x) = ProfiniteGrp.hatZNatCast d.val := by
  sorry

/-- The numbers of degree-one and degree-two closed points are `p - 1` and
`((p ^ 2 - 1) - (p - 1)) / 2`, respectively. -/
theorem sourcePoint_counts :
    Nat.card (sourcePoints p 1) = p - 1 ∧
      Nat.card (sourcePoints p 2) = ((p ^ 2 - 1) - (p - 1)) / 2 := by
  sorry

/-- The geometric tame kernel is the prime-to-characteristic procyclic group, and it admits
a degree-one geometric Frobenius lift acting by the inverse canonical prime unit. -/
theorem exists_source_kernel_identification :
    ∃ (e : (sourceExtension p).G ≃ₜ* Multiplicative (PadicInt.PrimeTo p))
      (F : (sourceExtension p).middle),
      (sourceExtension p).deg F = ProfiniteGrp.hatZOne ∧
      ∀ x : (sourceExtension p).G,
        e ((sourceExtension p).conjHom F x) =
          Multiplicative.ofAdd ((PadicInt.PrimeTo.natCastUnit p)⁻¹.val * (e x).toAdd) := by
  sorry

end MultiplicativeGroupTame
