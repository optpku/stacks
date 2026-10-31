/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.RingTheory.Ideal.Maps
public import ReasLib.Algebra.Module.Graded.HomogeneousMap
public import ReasLib.Algebra.Module.IdealPower.Submodule

@[expose] public section

noncomputable section

universe u v w

namespace Ideal

/-- The Rees module of `M` along `I`, with degree `n` component `I ^ n • ⊤`. -/
abbrev ReesModule {R : Type u} [CommSemiring R] (I : Ideal R) (M : Type v)
    [AddCommMonoid M] [Module R M] : Type v :=
  DirectSum ℕ (fun n ↦ PowerSubmodule.stage I M n)

namespace ReesModule

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- Insert an element of `I ^ n • ⊤` into degree `n` of the Rees module. -/
def of (I : Ideal R) (M : Type v) [AddCommMonoid M] [Module R M] (n : ℕ) :
    PowerSubmodule.stage I M n →ₗ[R] ReesModule I M :=
  DirectSum.lof R ℕ (fun d ↦ PowerSubmodule.stage I M d) n

/-- The degree-`n` submodule of a Rees module. -/
def grade (I : Ideal R) (M : Type v) [AddCommMonoid M] [Module R M] (n : ℕ) :
    Submodule R (ReesModule I M) :=
  LinearMap.range (of I M n)

set_option backward.privateInPublic true in
/-- The component map recovers an element inserted into its degree. -/
private theorem gradeEquiv_left_inv (I : Ideal R) (M : Type v) [AddCommMonoid M] [Module R M]
    (n : ℕ) (x : PowerSubmodule.stage I M n) :
    DirectSum.component R ℕ (fun d ↦ PowerSubmodule.stage I M d) n (of I M n x) = x := by
  simpa [of] using
    (DirectSum.component.lof_self (R := R)
      (M := fun d ↦ PowerSubmodule.stage I M d) n x)

set_option backward.privateInPublic true in
/-- Inserting the component of a homogeneous Rees element recovers that element. -/
private theorem gradeEquiv_right_inv (I : Ideal R) (M : Type v) [AddCommMonoid M] [Module R M]
    (n : ℕ) (x : grade I M n) :
    of I M n (DirectSum.component R ℕ (fun d ↦ PowerSubmodule.stage I M d) n x.1) = x.1 := by
  obtain ⟨y, hy⟩ := x.2
  rw [← hy]
  simp [of]

set_option backward.privateInPublic true in
/-- The explicit degree piece is linearly equivalent to its image in the Rees module. -/
def gradeEquiv (I : Ideal R) (M : Type v) [AddCommMonoid M] [Module R M] (n : ℕ) :
    PowerSubmodule.stage I M n ≃ₗ[R] grade I M n :=
  { (of I M n).rangeRestrict with
  invFun x := DirectSum.component R ℕ (fun d ↦ PowerSubmodule.stage I M d) n x.1
  left_inv x := gradeEquiv_left_inv I M n x
  right_inv x := Subtype.ext (gradeEquiv_right_inv I M n x) }

set_option backward.privateInPublic true in
/-- Recomposition is a left inverse to the componentwise homogeneous decomposition. -/
private theorem gradeDecomposition_left_inv (I : Ideal R) (M : Type v) [AddCommMonoid M] [Module R M] :
    Function.LeftInverse (DirectSum.coeAddMonoidHom (grade I M))
      (DirectSum.lmap (fun n ↦ (gradeEquiv I M n).toLinearMap)) := by
  intro x
  induction x using DirectSum.induction_on with
  | zero => simp
  | of n x =>
      simp only [DirectSum.lmap_of, DirectSum.coeAddMonoidHom_of]
      rfl
  | add x y hx hy =>
      simpa using congrArg₂ (· + ·) hx hy

set_option backward.privateInPublic true in
/-- The direct-sum recomposition is a right inverse to the homogeneous decomposition. -/
private theorem gradeDecomposition_right_inv (I : Ideal R) (M : Type v) [AddCommMonoid M] [Module R M] :
    Function.RightInverse (DirectSum.coeAddMonoidHom (grade I M))
      (DirectSum.lmap (fun n ↦ (gradeEquiv I M n).toLinearMap)) := by
  intro x
  induction x using DirectSum.induction_on with
  | zero => simp
  | of n x =>
      simp only [DirectSum.coeAddMonoidHom_of]
      obtain ⟨y, rfl⟩ := (gradeEquiv I M n).surjective x
      change DirectSum.lmap (fun d ↦ (gradeEquiv I M d).toLinearMap)
          (DirectSum.of (fun d ↦ PowerSubmodule.stage I M d) n y) =
        DirectSum.of (fun d ↦ grade I M d) n ((gradeEquiv I M n).toLinearMap y)
      exact DirectSum.lmap_of (f := fun d ↦ (gradeEquiv I M d).toLinearMap) n y
  | add x y hx hy =>
      simpa using congrArg₂ (· + ·) hx hy

set_option backward.privateInPublic true in
/-- The natural homogeneous pieces give the canonical decomposition of a Rees module. -/
instance gradeDecomposition (I : Ideal R) (M : Type v) [AddCommMonoid M] [Module R M] :
    DirectSum.Decomposition (grade I M) where
  decompose' x := DirectSum.lmap (fun n ↦ (gradeEquiv I M n).toLinearMap) x
  left_inv := gradeDecomposition_left_inv I M
  right_inv := gradeDecomposition_right_inv I M

/-- A coefficient in `I ^ (n * c)` also represents a coefficient in `(I ^ c) ^ n`. -/
theorem powerCoefficient_mem (I : Ideal R) {c n : ℕ} (g : (I ^ (n * c) : Ideal R)) :
    (g : R) ∈ (I ^ c) ^ n := by
  simpa [pow_mul, Nat.mul_comm] using g.2

/-- View a coefficient of `I ^ (n * c)` as a coefficient of `(I ^ c) ^ n`. -/
def powerCoefficient (I : Ideal R) {c n : ℕ} (g : (I ^ (n * c) : Ideal R)) :
    ((I ^ c) ^ n : Ideal R) :=
  ⟨g, powerCoefficient_mem I g⟩

/-- A positive power filtration stage maps into the corresponding stage of the original ideal. -/
theorem powerStage_le (I : Ideal R) (M : Type v) [AddCommMonoid M] [Module R M]
    {c : ℕ} (hc : 1 ≤ c) (n : ℕ) :
    PowerSubmodule.stage (I ^ c) M n ≤ PowerSubmodule.stage I M n := by
  change (I ^ c) ^ n • (⊤ : Submodule R M) ≤ I ^ n • (⊤ : Submodule R M)
  apply Submodule.smul_mono_left
  have hn : n ≤ n * c := by
    simpa using Nat.mul_le_mul_left n hc
  have hpow : I ^ (n * c) ≤ I ^ n := Ideal.pow_le_pow_right hn
  simpa [pow_mul, Nat.mul_comm] using hpow

set_option backward.privateInPublic true in
/-- The grading law for the componentwise inclusion of powered Rees modules. -/
private theorem powerInclusion_mapsTo (I : Ideal R) (M : Type v) [AddCommMonoid M] [Module R M]
    {c : ℕ} (hc : 1 ≤ c) :
    DirectSum.lmap (fun n ↦ Submodule.inclusion (powerStage_le I M hc n)) ∈
      GradedModule.MapsTo R (grade (I ^ c) M) (grade I M) id := by
  rw [GradedModule.mem_mapsTo_iff]
  intro n x hx
  rcases hx with ⟨y, rfl⟩
  refine ⟨⟨y, powerStage_le I M hc n y.2⟩, ?_⟩
  simp only [of, DirectSum.lmap_lof]
  exact congrArg (of I M n) (Subtype.ext (by rfl))

set_option backward.privateInPublic true in
/-- The degree-preserving inclusion from the Rees module of `I ^ c` to that of `I`. -/
def powerInclusion (I : Ideal R) (M : Type v) [AddCommMonoid M] [Module R M]
    {c : ℕ} (hc : 1 ≤ c) :
    GradedModule.MapsTo R (grade (I ^ c) M) (grade I M) id :=
  ⟨DirectSum.lmap (fun n ↦ Submodule.inclusion (powerStage_le I M hc n)),
    powerInclusion_mapsTo I M hc⟩

/-- The Rees-module power inclusion is the componentwise filtration inclusion. -/
theorem powerInclusion_of (I : Ideal R) (M : Type v) [AddCommMonoid M] [Module R M]
    {c : ℕ} (hc : 1 ≤ c) (n : ℕ) (x : PowerSubmodule.stage (I ^ c) M n) :
    GradedModule.MapsTo.toLinearMap (powerInclusion I M hc) (of (I ^ c) M n x) =
      of I M n ⟨x, powerStage_le I M hc n x.2⟩ := by
  change DirectSum.lmap (fun n ↦ Submodule.inclusion (powerStage_le I M hc n))
      (of (I ^ c) M n x) = of I M n ⟨x, powerStage_le I M hc n x.2⟩
  simp only [of, DirectSum.lmap_lof]
  rfl

/-- The image of an ideal element under a ring map, retained in the mapped ideal. -/
def mappedGenerator {S : Type w} [CommSemiring S] (I : Ideal R) (α : R →+* S)
    (g : I) : I.map α :=
  ⟨α g, Ideal.mem_map_of_mem α g.2⟩

/-- Multiplying by a mapped coefficient of `I ^ (n * c)` lands in degree `n` of the
Rees module for `(I.map α) ^ c`. -/
theorem mapped_smul_mem_stage {S : Type w} [CommSemiring S] (I : Ideal R)
    (α : R →+* S) {N : Type v} [AddCommMonoid N] [Module S N]
    {c n : ℕ} (g : (I ^ (n * c) : Ideal R)) (x : N) :
    α g • x ∈ PowerSubmodule.stage ((I.map α) ^ c) N n := by
  change α (g : R) • x ∈ ((I.map α) ^ c) ^ n • (⊤ : Submodule S N)
  have hg : α (g : R) ∈ (I.map α) ^ (n * c) := by
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem α g.2
  have hg' : α (g : R) ∈ ((I.map α) ^ c) ^ n := by
    simpa [pow_mul, Nat.mul_comm] using hg
  exact Submodule.smul_mem_smul hg' (Submodule.mem_top)

/-- Insert the product of a mapped coefficient and a module element in its Rees degree. -/
def mappedOf {S : Type w} [CommSemiring S] (I : Ideal R) (α : R →+* S)
    {N : Type v} [AddCommMonoid N] [Module S N] {c n : ℕ}
    (g : (I ^ (n * c) : Ideal R)) (x : N) : ReesModule ((I.map α) ^ c) N :=
  of ((I.map α) ^ c) N n ⟨α g • x, mapped_smul_mem_stage I α g x⟩

/-- The mapped generator has the prescribed homogeneous component. -/
theorem mappedOf_eq (I : Ideal R) {S : Type w} [CommSemiring S] (α : R →+* S)
    {N : Type v} [AddCommMonoid N] [Module S N] {c n : ℕ}
    (g : (I ^ (n * c) : Ideal R)) (x : N) :
    mappedOf I α g x =
      of ((I.map α) ^ c) N n ⟨α g • x, mapped_smul_mem_stage I α g x⟩ := by
  rfl

end ReesModule
end Ideal
