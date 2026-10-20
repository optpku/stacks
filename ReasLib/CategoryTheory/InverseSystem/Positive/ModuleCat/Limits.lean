module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import ReasLib.CategoryTheory.InverseSystem.Positive.Limits
public import ReasLib.CategoryTheory.InverseSystem.Positive.ModuleCat
public import ReasLib.CategoryTheory.InverseSystem.OrderDual.ModuleCat.Limits

/-!
# Limits of Positive Module Inverse Systems

This leaf specializes the generic order-dual linear limit compatibility to the positive-natural
successor map.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.PNatInverseSystem

variable {R : Type u} [Ring R]

/-- The linear map underlying the canonical projection from the limit of a positive inverse system
to its stage `n`. -/
abbrev limitProjectionLinearMap (F : PNatInverseSystem (ModuleCat.{v} R)) [HasLimit F]
    (n : ℕ+) :
    (limit F : ModuleCat.{v} R) →ₗ[R] F.stage n :=
  OrderDualInverseSystem.limitProjectionLinearMap F n

/-- The linear limit projection to the successor stage followed by the successor transition is
the current-stage linear limit projection. -/
theorem limitProjectionLinearMap_comp_stepLinearMap
    (F : PNatInverseSystem (ModuleCat.{v} R)) [HasLimit F] (n : ℕ+) :
    (F.stepLinearMap n).comp (F.limitProjectionLinearMap (n + 1)) =
      F.limitProjectionLinearMap n := sorry

/-- The coordinate at `m` of the compatible lift of an element at stage `n`:
project down when `m ≤ n`, and recursively lift through successor maps otherwise. -/
def limitProjectionSectionStage
    (F : PNatInverseSystem (ModuleCat.{v} R))
    (h_step : ∀ n : ℕ+, Function.Surjective (F.stepLinearMap n))
    (n : ℕ+) (x : F.stage n) (m : ℕ+) : F.stage m :=
  PNat.recOn m
    (F.transitionLinearMap (one_le : (1 : ℕ+) ≤ n) x)
    (fun k y ↦ if h : k + 1 ≤ n then F.transitionLinearMap h x
      else Function.surjInv (h_step k) y)

private theorem limitProjectionSectionStage_of_le
    (F : PNatInverseSystem (ModuleCat.{v} R))
    (h_step : ∀ n : ℕ+, Function.Surjective (F.stepLinearMap n))
    (n : ℕ+) (x : F.stage n) (m : ℕ+) (hm : m ≤ n) :
    limitProjectionSectionStage F h_step n x m = F.transitionLinearMap hm x := by
  cases m using PNat.recOn with
  | one => rfl
  | succ m => simp only [limitProjectionSectionStage, PNat.recOn_succ, dif_pos hm]

/-- The recursively chosen coordinates form a compatible family. -/
theorem limitProjectionSectionStage_naturality
    (F : PNatInverseSystem (ModuleCat.{v} R))
    (h_step : ∀ n : ℕ+, Function.Surjective (F.stepLinearMap n))
    (n : ℕ+) (x : F.stage n) {i j : OrderDual ℕ+} (f : i ⟶ j) :
    (F.map f).hom (limitProjectionSectionStage F h_step n x (OrderDual.ofDual i)) =
      limitProjectionSectionStage F h_step n x (OrderDual.ofDual j) := sorry

/-- A section of the projection to stage `n`, obtained by projecting below `n`
and recursively choosing preimages under the surjective successor maps above `n`.
The section need not be linear. -/
def limitProjectionSection
    (F : PNatInverseSystem (ModuleCat.{v} R)) [HasLimit F]
    (h_step : ∀ n : ℕ+, Function.Surjective (F.stepLinearMap n))
    (n : ℕ+) (x : F.stage n) : (limit F : ModuleCat.{v} R) :=
  (Types.isLimitEquivSections
    (isLimitOfPreserves (forget (ModuleCat.{v} R)) (limit.isLimit F))).symm
      ⟨fun i ↦ limitProjectionSectionStage F h_step n x (OrderDual.ofDual i),
        fun f ↦ limitProjectionSectionStage_naturality F h_step n x f⟩

/-- The recursively lifted compatible family projects to the prescribed element. -/
theorem limitProjectionLinearMap_section
    (F : PNatInverseSystem (ModuleCat.{v} R)) [HasLimit F]
    (h_step : ∀ n : ℕ+, Function.Surjective (F.stepLinearMap n))
    (n : ℕ+) (x : F.stage n) :
    F.limitProjectionLinearMap n (F.limitProjectionSection h_step n x) = x := by
  change ((forget (ModuleCat.{v} R)).mapCone (limit.cone F)).π.app _ _ = x
  rw [limitProjectionSection, Types.isLimitEquivSections_symm_apply]
  change limitProjectionSectionStage F h_step n x n = x
  rw [limitProjectionSectionStage_of_le F h_step n x n le_rfl]
  exact congrArg (fun f : F.stage n →ₗ[R] F.stage n ↦ f x)
    (F.transitionLinearMap_refl n)

/-- Surjectivity of all successor linear maps makes every canonical limit projection surjective. -/
theorem limitProjectionLinearMap_surjective_of_stepLinearMap_surjective
    (F : PNatInverseSystem (ModuleCat.{v} R)) [HasLimit F]
    (h_step : ∀ n : ℕ+, Function.Surjective (F.stepLinearMap n))
    (n : ℕ+) :
    Function.Surjective (F.limitProjectionLinearMap n) :=
  fun x ↦ ⟨F.limitProjectionSection h_step n x, F.limitProjectionLinearMap_section h_step n x⟩

end CategoryTheory.PNatInverseSystem
