/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Module
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Shifts of Differential Graded Modules

This leaf owns the canonical integer shift for right differential graded
modules, its action on morphisms, and the corresponding computation API.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra R}

/-- Reassociates the target degree of the shifted differential. -/
theorem shift_d_index (n k : ℤ) :
    n + k + 1 = (n + 1) + k := sorry

/-- Reassociates the target degree of the shifted right action. -/
theorem shift_smul_index (p i k : ℤ) :
    (p + k) + i = (p + i) + k := sorry

/-- The differential of a shifted right DG module squares to zero. -/
theorem shiftDsq (M : DifferentialGradedModule A) (k n : ℤ) (x : M.X (n + k)) :
    ModuleCat.castLinearMap
      (congrArg M.X (shift_d_index (n + 1) k))
      ((k.negOnePow : R) • M.d (n + 1 + k))
      (ModuleCat.castLinearMap
        (congrArg M.X (shift_d_index n k))
        ((k.negOnePow : R) • M.d (n + k)) x) = 0 := sorry

/-- The shifted right action satisfies its unit law. -/
theorem shiftSmulOne (M : DifferentialGradedModule A) (k : ℤ)
    (r : R) (p : ℤ) (x : M.X (p + k)) :
    ModuleCat.castLinearMap
      (congrArg (fun n : ℤ ↦ ModuleCat.of R (A.X 0 →ₗ[R] M.X n)) (shift_smul_index p 0 k))
      (M.smul (p + k) 0) x (r • A.one) =
      cast (DifferentialGradedModule.zeroActionTarget (M := fun n : ℤ ↦ M.X (n + k)) p) (r • x) := sorry

/-- The shifted right action respects homogeneous multiplication in the algebra. -/
theorem shiftSmulMul (M : DifferentialGradedModule A) (k p i j : ℤ)
    (x : M.X (p + k)) (a : A.X i) (b : A.X j) :
    ModuleCat.castLinearMap
      (congrArg (fun n : ℤ ↦ ModuleCat.of R (A.X (i + j) →ₗ[R] M.X n))
        (shift_smul_index p (i + j) k))
      (M.smul (p + k) (i + j)) x (A.mul i j a b) =
      cast (DifferentialGradedModule.mulActionTarget (M := fun n : ℤ ↦ M.X (n + k)) p i j)
        (ModuleCat.castLinearMap
          (congrArg (fun n : ℤ ↦ ModuleCat.of R (A.X j →ₗ[R] M.X n))
            (shift_smul_index (p + i) j k))
          (M.smul ((p + i) + k) j)
          (ModuleCat.castLinearMap
            (congrArg (fun n : ℤ ↦ ModuleCat.of R (A.X i →ₗ[R] M.X n))
              (shift_smul_index p i k))
            (M.smul (p + k) i) x a) b) := sorry

/-- The shifted differential satisfies the graded Leibniz rule. -/
theorem shiftCommD (M : DifferentialGradedModule A) (k p i : ℤ)
    (x : M.X (p + k)) (a : A.X i) :
    ModuleCat.castLinearMap
      (congrArg M.X (shift_d_index (p + i) k))
      ((k.negOnePow : R) • M.d (p + i + k))
      (ModuleCat.castLinearMap
        (congrArg (fun n : ℤ ↦ ModuleCat.of R (A.X i →ₗ[R] M.X n))
          (shift_smul_index p i k))
        (M.smul (p + k) i) x a) =
      cast (DifferentialGradedModule.dLeftActionTarget (M := fun n : ℤ ↦ M.X (n + k)) p i)
        (ModuleCat.castLinearMap
          (congrArg (fun n : ℤ ↦ ModuleCat.of R (A.X i →ₗ[R] M.X n))
            (shift_smul_index (p + 1) i k))
          (M.smul (p + 1 + k) i)
          (ModuleCat.castLinearMap
            (congrArg M.X (shift_d_index p k))
            ((k.negOnePow : R) • M.d (p + k)) x) a) +
        (p.negOnePow : R) •
          cast (DifferentialGradedModule.dRightActionTarget (M := fun n : ℤ ↦ M.X (n + k)) p i)
            (ModuleCat.castLinearMap
              (congrArg (fun n : ℤ ↦ ModuleCat.of R (A.X (i + 1) →ₗ[R] M.X n))
                (shift_smul_index p (i + 1) k))
              (M.smul (p + k) (i + 1)) x (A.d i a)) := sorry

/-- A shifted morphism commutes with the shifted differential. -/
theorem shiftMapCommD {M N : DifferentialGradedModule A} (f : M ⟶ N) (k n : ℤ)
    (x : M.X (n + k)) :
    f.hom (n + 1 + k)
      (ModuleCat.castLinearMap
        (congrArg M.X (shift_d_index n k))
        ((k.negOnePow : R) • M.d (n + k)) x) =
      ModuleCat.castLinearMap
        (congrArg N.X (shift_d_index n k))
        ((k.negOnePow : R) • N.d (n + k))
        (f.hom (n + k) x) := sorry

/-- A shifted morphism remains compatible with the shifted right action. -/
theorem shiftMapCommSmul {M N : DifferentialGradedModule A} (f : M ⟶ N)
    (k p i : ℤ) (x : M.X (p + k)) (a : A.X i) :
    f.hom (p + i + k)
      (ModuleCat.castLinearMap
        (congrArg (fun n : ℤ ↦ ModuleCat.of R (A.X i →ₗ[R] M.X n))
          (shift_smul_index p i k))
        (M.smul (p + k) i) x a) =
      ModuleCat.castLinearMap
        (congrArg (fun n : ℤ ↦ ModuleCat.of R (A.X i →ₗ[R] N.X n))
          (shift_smul_index p i k))
        (N.smul (p + k) i)
        (f.hom (p + k) x) a := sorry

/-- Definition 22.4.3: the canonical integer shift of a right differential graded module. -/
@[stacks 09JL]
def shift (M : DifferentialGradedModule A) (k : ℤ) : DifferentialGradedModule A where
  X n := M.X (n + k)
  d n :=
    ModuleCat.castLinearMap (congrArg M.X (shift_d_index n k)) ((k.negOnePow : R) • M.d (n + k))
  smul p i :=
    ModuleCat.castLinearMap
      (congrArg (fun n : ℤ ↦ ModuleCat.of R (A.X i →ₗ[R] M.X n)) (shift_smul_index p i k))
      (M.smul (p + k) i)
  d_sq := shiftDsq M k
  smul_one := shiftSmulOne M k
  smul_mul := shiftSmulMul M k
  comm_d := shiftCommD M k

/-- Shift a right-DG-module morphism degreewise. -/
@[stacks 09JL "shift on DG-module morphisms"]
def shiftMap {M N : DifferentialGradedModule A} (f : M ⟶ N) (k : ℤ) :
    shift M k ⟶ shift N k where
  hom n := f.hom (n + k)
  comm_d := shiftMapCommD f k
  comm_smul := shiftMapCommSmul f k

@[inherit_doc shift]
scoped[DifferentialGradedModule] notation:max M:max "[" k:max "]" => shift M k

open scoped DifferentialGradedModule

/-- The degree-`n` term of `M[k]` is `M^(n + k)`. -/
@[simp, stacks 09JL "shift object component"] theorem shift_X (M : DifferentialGradedModule A) (k n : ℤ) :
    (M[k]).X n = M.X (n + k) := sorry

/-- The shifted differential is `(-1)^k d_M` after reindexing. -/
@[simp, stacks 09JL "shift differential computation"] theorem shift_d (M : DifferentialGradedModule A) (k n : ℤ) :
    (M[k]).d n =
      ModuleCat.castLinearMap
        (congrArg M.X (shift_d_index n k))
        ((k.negOnePow : R) • M.d (n + k)) := sorry

/-- The shifted right action is the original action after target reindexing. -/
@[simp, stacks 09JL "shift action computation"] theorem shift_smul (M : DifferentialGradedModule A) (k p i : ℤ) :
    (M[k]).smul p i =
      ModuleCat.castLinearMap
        (congrArg (fun n : ℤ ↦ ModuleCat.of R (A.X i →ₗ[R] M.X n))
          (shift_smul_index p i k))
        (M.smul (p + k) i) := sorry

/-- The shifted morphism is the original degreewise map after reindexing. -/
@[simp, stacks 09JL "shift morphism computation"] theorem shift_map_hom {M N : DifferentialGradedModule A} (f : M ⟶ N) (k n : ℤ) :
    (shiftMap f k).hom n = f.hom (n + k) := sorry

/-- The shifted morphism acts through the original map after reindexing. -/
@[simp] theorem shift_map_apply {M N : DifferentialGradedModule A} (f : M ⟶ N) (k n : ℤ)
    (x : (M[k]).X n) :
    (shiftMap f k).hom n x = f.hom (n + k) x := sorry

/-- Shifting preserves identity morphisms. -/
@[simp, stacks 09JL "shift identity morphism"] theorem shiftMap_id (M : DifferentialGradedModule A) (k : ℤ) :
    shiftMap (𝟙 M) k = 𝟙 (M[k]) := sorry

/-- Shifting preserves composition of morphisms. -/
@[simp, stacks 09JL "shift composition of morphisms"] theorem shiftMap_comp {L M N : DifferentialGradedModule A} (f : L ⟶ M) (g : M ⟶ N)
    (k : ℤ) :
    shiftMap (f ≫ g) k = shiftMap f k ≫ shiftMap g k := sorry

end DifferentialGradedModule
