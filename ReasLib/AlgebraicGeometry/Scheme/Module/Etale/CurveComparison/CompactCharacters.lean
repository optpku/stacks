/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.CharacterModule.Evaluation
public import Mathlib.Topology.Algebra.PontryaginDual
public import Mathlib.Topology.Algebra.Module.Basic

@[expose] public section

noncomputable section

universe u v

namespace CompactCharacters

/-- The finite annihilator in Q/Z, not Q/Z with an assumed compact topology. -/
def Roots (n : ℕ) := {x : AddCircle (1 : ℚ) // n • x = 0}

instance (n : ℕ) : TopologicalSpace (Roots n) := ⊥
instance (n : ℕ) : DiscreteTopology (Roots n) := ⟨rfl⟩

theorem roots_finite (n : ℕ) (hn : n ≠ 0) : Finite (Roots n) := by
  sorry

variable (Λ : Type u) [CommRing Λ] [Finite Λ]
variable (M : Type v) [AddCommGroup M] [Module Λ M]

/-- Additive order of the finite coefficient ring annihilates every module. -/
theorem module_annihilated (m : M) : Nat.card Λ • m = 0 := by
  sorry

def evaluationCoordinates (χ : CharacterModule M) : M → Roots (Nat.card Λ) :=
  fun m ↦ ⟨χ m, by
    rw [← map_nsmul, module_annihilated Λ M, map_zero]⟩

/-- Keep this compact view separate from discrete character modules. -/
def Dual (Λ : Type u) (M : Type v) [AddCommGroup M] := CharacterModule M

instance : AddCommGroup (Dual Λ M) := inferInstanceAs (AddCommGroup (CharacterModule M))
instance : Module Λ (Dual Λ M) := inferInstanceAs (Module Λ (CharacterModule M))

/-- Pointwise convergence in the product of finite annihilators. -/
instance : TopologicalSpace (Dual Λ M) :=
  TopologicalSpace.induced (evaluationCoordinates Λ M) inferInstance

theorem coordinates_injective : Function.Injective (evaluationCoordinates Λ M) := by
  intro a b h
  apply CharacterModule.ext
  intro m
  exact congrArg Subtype.val (congrFun h m)

/-- Additivity equations cut out a closed subset of the product. -/
theorem coordinates_closed : IsClosed (Set.range (evaluationCoordinates Λ M)) := by
  sorry

instance : CompactSpace (Dual Λ M) := by
  -- Finite discrete annihilator, Tychonoff, and the closed additive equations.
  sorry

instance : T2Space (Dual Λ M) := by sorry
instance : TotallyDisconnectedSpace (Dual Λ M) := by sorry
instance : IsTopologicalAddGroup (Dual Λ M) := by sorry
instance : ContinuousConstSMul Λ (Dual Λ M) := by sorry

def evalAt (m : M) : Dual Λ M →+ AddCircle (1 : ℚ) :=
  { toFun := fun χ ↦ (show CharacterModule M from χ) m
    map_zero' := rfl
    map_add' := fun _ _ ↦ rfl }

/-- Evaluation actually lands in a finite coordinate. -/
theorem continuous_coordinate (m : M) :
    Continuous (fun χ : Dual Λ M ↦ evaluationCoordinates Λ M χ m) := by
  sorry

/-- Precomposition on actual characters. -/
def map {N : Type v} [AddCommGroup N] [Module Λ N] (f : M →ₗ[Λ] N) :
    Dual Λ N →ₗ[Λ] Dual Λ M := CharacterModule.dual f

theorem continuous_map {N : Type v} [AddCommGroup N] [Module Λ N]
    (f : M →ₗ[Λ] N) : Continuous (map Λ M f) := by
  sorry

/-- Finite double duality inverts the actual evaluation map. -/
theorem finite_eval_bijective [Finite M] :
    Function.Bijective (CharacterModule.evalLinear Λ :
      M →ₗ[Λ] CharacterModule (CharacterModule M)) := by
  sorry

def finiteDoubleDual [Finite M] : M ≃ₗ[Λ] CharacterModule (CharacterModule M) :=
  LinearEquiv.ofBijective (CharacterModule.evalLinear Λ) (finite_eval_bijective Λ M)

theorem finiteDoubleDual_apply [Finite M] (m : M) (χ : CharacterModule M) :
    finiteDoubleDual Λ M m χ = χ m := rfl

/-- Continuous characters of the compact dual, with continuity tested in the
finite annihilator, not all algebraic characters of an infinite compact group. -/
def continuousCharacters : Submodule Λ (CharacterModule (Dual Λ M)) where
  carrier := {χ | Continuous (evaluationCoordinates Λ (Dual Λ M) χ)}
  zero_mem' := by sorry
  add_mem' := by sorry
  smul_mem' := by sorry

/-- Continuous double-dual evaluation, defined on the original elements. -/
def continuousEvaluation : M →ₗ[Λ] continuousCharacters Λ M :=
  LinearMap.codRestrict (continuousCharacters Λ M)
    (CharacterModule.evalLinear Λ) (by
      intro m
      exact continuous_coordinate Λ M m)

/-- Bounded-torsion Pontryagin reflexivity: every continuous character factors
through finitely many coordinates and is evaluation at an element of M. -/
theorem continuousEvaluation_bijective :
    Function.Bijective (continuousEvaluation Λ M) := by
  sorry

def continuousDoubleDual : M ≃ₗ[Λ] continuousCharacters Λ M :=
  LinearEquiv.ofBijective (continuousEvaluation Λ M)
    (continuousEvaluation_bijective Λ M)

end CompactCharacters
