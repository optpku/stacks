/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.MultiplicativeGroup.TameDegreeExtension
public import stacks_project.Chap64.Remark_64_30_1_ContinuousFormula

/-!
# The geometric a = 1 case of Example 64.30.2

The group, degree map, and closed points are the constructed tame geometric
data. Labels and kernel identifications are source conclusions, not inputs
or selected witnesses used to define the data.
-/

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open ProfiniteGrp.ContinuousTrace
noncomputable section

namespace MultiplicativeGroupTame
variable (p : ℕ) [Fact p.Prime]

/-- Only the carrier universe changes to match the original DegreeExtension universe. -/
abbrev liftedSourcePoints (d : ℕ+) : Type 1 := ULift.{1} (sourcePoints p d)

instance liftedSourcePoints_fintype (d : ℕ+) : Fintype (liftedSourcePoints p d) :=
  Fintype.ofFinite _

/-- The original numerical owner sums the same actual point labels after canonical ULift. -/
def sourceTraceData
    (F : ∀ d : ℕ+, sourcePoints p d → ConjClasses (sourceExtension p).middle)
    (hdeg : ∀ (d : ℕ+) (x : sourcePoints p d),
      (sourceExtension p).degClass (F d x) = ProfiniteGrp.hatZNatCast d.val) :
    AbstractTraceData (sourceExtension p) :=
  AbstractTraceData.ofFiniteSets p (Nat.Prime.one_le (Fact.out : p.Prime))
    (ι := liftedSourcePoints p) (fun d x ↦ F d x.down) (fun d x ↦ hdeg d x.down)

theorem sourceTraceData_q
    (F : ∀ d : ℕ+, sourcePoints p d → ConjClasses (sourceExtension p).middle)
    (hdeg : ∀ (d : ℕ+) (x : sourcePoints p d),
      (sourceExtension p).degClass (F d x) = ProfiniteGrp.hatZNatCast d.val) :
    (sourceTraceData p F hdeg).q = p := rfl

/-- ULift has not replaced the geometric closed-point family by a different counting set. -/
theorem liftedSourcePoints_card (d : ℕ+) :
    Nat.card (liftedSourcePoints p d) = Nat.card (sourcePoints p d) :=
  Nat.card_congr Equiv.ulift

/-- The source's a = 1 realization. Every geometric datum is fixed beforehand.
The actual labels, their degree law, and the kernel identification are conclusions.
The trace predicate is the full continuous formula for arbitrary finite rings,
all finite projective continuous modules and every positive n. -/
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
