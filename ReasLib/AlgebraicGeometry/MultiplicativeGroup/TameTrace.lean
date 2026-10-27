/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.MultiplicativeGroup.TameDegreeExtension
public import ReasLib.Topology.Algebra.Category.ProfiniteGrp.AbstractTrace

/-!
# Continuous trace data for the tame multiplicative group over a prime field

The closed-point families supply numerical trace data on the tame degree extension.
Geometric Frobenius acts by the inverse canonical prime unit on the geometric kernel.
-/

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open ProfiniteGrp.ContinuousTrace
noncomputable section

namespace MultiplicativeGroupTame
variable (p : ℕ) [Fact p.Prime]

/-- The closed-point family lifted to the universe of the tame degree extension. -/
abbrev liftedSourcePoints (d : ℕ+) : Type 1 := ULift.{1} (sourcePoints p d)

/-- The universe lift of each closed-point family admits a finite enumeration. -/
instance liftedSourcePoints_fintype (d : ℕ+) : Fintype (liftedSourcePoints p d) :=
  Fintype.ofFinite _

/-- Numerical trace data obtained by summing the closed-point labels after universe lifting. -/
def sourceTraceData
    (F : ∀ d : ℕ+, sourcePoints p d → ConjClasses (sourceExtension p).middle)
    (hdeg : ∀ (d : ℕ+) (x : sourcePoints p d),
      (sourceExtension p).degClass (F d x) = ProfiniteGrp.hatZNatCast d.val) :
    AbstractTraceData (sourceExtension p) :=
  AbstractTraceData.ofFiniteSets p (Nat.Prime.one_le (Fact.out : p.Prime))
    (ι := liftedSourcePoints p) (fun d x ↦ F d x.down) (fun d x ↦ hdeg d x.down)

/-- The distinguished integer of the closed-point trace data is the characteristic prime. -/
theorem sourceTraceData_q
    (F : ∀ d : ℕ+, sourcePoints p d → ConjClasses (sourceExtension p).middle)
    (hdeg : ∀ (d : ℕ+) (x : sourcePoints p d),
      (sourceExtension p).degClass (F d x) = ProfiniteGrp.hatZNatCast d.val) :
    (sourceTraceData p F hdeg).q = p := rfl

/-- Universe lifting preserves the cardinality of each geometric closed-point family. -/
theorem liftedSourcePoints_card (d : ℕ+) :
    Nat.card (liftedSourcePoints p d) = Nat.card (sourcePoints p d) :=
  Nat.card_congr Equiv.ulift

/-- The tame multiplicative-group degree extension over a prime field admits compatible
Frobenius labels satisfying the full continuous trace formula. Its geometric kernel is the
prime-to-characteristic procyclic group, with geometric Frobenius acting by the inverse
prime unit, and its first two closed-point counts give integral representative one. -/
@[stacks 03VQ]
theorem tame_multiplicative_realization :
    ∃ F : ∀ d : ℕ+, sourcePoints p d → ConjClasses (sourceExtension p).middle,
      ∃ hdeg : ∀ (d : ℕ+) (x : sourcePoints p d),
          (sourceExtension p).degClass (F d x) = ProfiniteGrp.hatZNatCast d.val,
        LabelsMatchOrbit p F ∧
        IsAbstractTraceFormula (sourceExtension p) (sourceTraceData p F hdeg) ∧
        (∃ (e : (sourceExtension p).G ≃ₜ* Multiplicative (PadicInt.PrimeTo p))
            (geometricFrobenius : (sourceExtension p).middle),
          (sourceExtension p).deg geometricFrobenius = ProfiniteGrp.hatZOne ∧
          ∀ x : (sourceExtension p).G,
            e ((sourceExtension p).conjHom geometricFrobenius x) =
              Multiplicative.ofAdd ((PadicInt.PrimeTo.natCastUnit p)⁻¹.val * (e x).toAdd)) ∧
        (p : PadicInt.PrimeTo p) * (PadicInt.PrimeTo.natCastUnit p)⁻¹.val = 1 ∧
        Nat.card (sourcePoints p 1) = p - 1 ∧
        Nat.card (sourcePoints p 2) = ((p ^ 2 - 1) - (p - 1)) / 2 := by
  sorry

end MultiplicativeGroupTame
