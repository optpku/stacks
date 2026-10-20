/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.MultiplicativeGroup.TameLabels
public import ReasLib.Topology.Algebra.Category.ProfiniteGrp.DegreeExtension
public import ReasLib.NumberTheory.Padics.PrimeTo.Basic

/-! The original source's degree-extension interface on the constructed tame group. -/

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme TopologicalSpace
noncomputable section

namespace MultiplicativeGroupTame
variable (p : ℕ) [Fact p.Prime]

/-- The actual geometric base point used by this source instance. -/
abbrev sourcePoint := genericPoint (ZMod p)

/-- Surjectivity comes from constant-cover restriction and its specified Frobenius normalization. -/
theorem sourceDegree_surjective : Function.Surjective (degreeToIntegers p (sourcePoint p)) :=
  degreeToIntegers_surjective p (sourcePoint p)

/-- Original DegreeExtension, with the specified group and degree and no new data choices. -/
def sourceExtension : ProfiniteGrp.DegreeExtension.{1} where
  middle := fundamentalGroup (ZMod p) (sourcePoint p)
  deg := degreeToIntegers p (sourcePoint p)
  deg_surjective := sourceDegree_surjective p

theorem sourceExtension_middle : (sourceExtension p).middle =
    fundamentalGroup (ZMod p) (sourcePoint p) := rfl

theorem sourceExtension_degree : (sourceExtension p).deg =
    degreeToIntegers p (sourcePoint p) := rfl

theorem sourceExtension_kernel : (sourceExtension p).kerClosed =
    geometricKernel p (sourcePoint p) := rfl

/-- Exactly the actual point family; no auxiliary counting family replaces it. -/
abbrev sourcePoints (d : ℕ+) := points (ZMod p) d

/-- Quotient labels match the already constructed orbit on every actual representative. -/
def LabelsMatchOrbit
    (F : ∀ d : ℕ+, sourcePoints p d → ConjClasses (sourceExtension p).middle) : Prop :=
  ∀ (d : ℕ+) (x : sourcePoints p d) (g : (sourceExtension p).middle),
    g ∈ labels (ZMod p) (sourcePoint p) d x ↔ ConjClasses.mk g = F d x

/-- Quotient labels and their degree laws are conclusions about the specified point family. -/
theorem exists_source_labels :
    ∃ F : ∀ d : ℕ+, sourcePoints p d → ConjClasses (sourceExtension p).middle,
      LabelsMatchOrbit p F ∧
      ∀ (d : ℕ+) (x : sourcePoints p d),
        (sourceExtension p).degClass (F d x) = ProfiniteGrp.hatZNatCast d.val := by
  sorry

/-- The two counts refer to the same actual families used by the label and trace contracts. -/
theorem sourcePoint_counts :
    Nat.card (sourcePoints p 1) = p - 1 ∧
      Nat.card (sourcePoints p 2) = ((p ^ 2 - 1) - (p - 1)) / 2 := by
  sorry

/-- A finite-field geometric Frobenius acts on the geometric tame kernel by p inverse.
Both the lift and the identification are conclusions, not inputs or selected definitions. -/
theorem exists_source_kernel_identification :
    ∃ (e : (sourceExtension p).G ≃ₜ* Multiplicative (PadicInt.PrimeTo p))
      (F : (sourceExtension p).middle),
      (sourceExtension p).deg F = ProfiniteGrp.hatZOne ∧
      ∀ x : (sourceExtension p).G,
        e ((sourceExtension p).conjHom F x) =
          Multiplicative.ofAdd ((PadicInt.PrimeTo.natCastUnit p)⁻¹.val * (e x).toAdd) := by
  sorry

end MultiplicativeGroupTame
