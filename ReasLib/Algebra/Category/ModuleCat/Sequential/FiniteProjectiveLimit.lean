/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Flat.Basic
public import ReasLib.Algebra.Category.ModuleCat.FiniteProjective
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Sequential.DerivedLimit
public import ReasLib.RingTheory.Ideal.LocallyNilpotent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite projective inverse limits of sequential module systems

For a sequential inverse system of commutative rings, this file owns the two canonical
base-change morphisms attached to a compatible varying-ring module system.  It also records the
finite-projective inverse-limit criterion of Lemma 15.13.4.

@stack 0D4B
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace CategoryTheory.SequentialInverseSystem.ModuleSystem.FiniteProjectiveLimit

variable (A : ℕ → Type u) [∀ n, CommRing (A n)]
variable (ρ : ∀ n, A (n + 1) →+* A n)

/-- The `n`th module of a sequential varying-ring module system. -/
@[stacks 0D4B "stage module"]
abbrev stage (M : SeqRingMod.{u, u} A ρ) (n : ℕ) : ModuleCat.{u} (A n) :=
  (sequentialRingedModuleEvaluation A ρ n).obj M

/-- The module over `lim Aₙ` obtained by taking the inverse limit of a varying-ring module
system. -/
@[stacks 0D4B "inverse-limit module"]
abbrev inverseLimit (M : SeqRingMod.{u, u} A ρ) :
    ModuleCat.{u} (DerivedLimit.limitRing A ρ) :=
  (DerivedLimit.ringedModuleInverseLimitFunctor A ρ).obj M

/-- The successor transition of a varying-ring module, viewed after restriction of scalars. -/
@[stacks 0D4B "successor transition of the module system"]
abbrev stageTransition (M : SeqRingMod.{u, u} A ρ) (n : ℕ) :
    stage A ρ M (n + 1) ⟶
      (ModuleCat.restrictScalars ((sequentialRingSystem A ρ).stepMap n).hom).obj
        (stage A ρ M n) :=
  (sequentialRingedModuleEvaluationStep A ρ n).app M

/-- The canonical base-change morphism
`Aₙ ⊗[Aₙ₊₁] Mₙ₊₁ ⟶ Mₙ` induced by the successor transition. -/
@[stacks 0D4B "successor base-change comparison"]
noncomputable def stageBaseChangeComparison
    (M : SeqRingMod.{u, u} A ρ) (n : ℕ) :
    (ModuleCat.extendScalars ((sequentialRingSystem A ρ).stepMap n).hom).obj
        (stage A ρ M (n + 1)) ⟶ stage A ρ M n :=
  ((ModuleCat.extendRestrictScalarsAdj
      ((sequentialRingSystem A ρ).stepMap n).hom).homEquiv _ _).symm
    (stageTransition A ρ M n)

/-- The projection from the inverse-limit module to the `n`th stage, viewed after restriction of
scalars along `lim Aₙ ⟶ Aₙ`. -/
@[stacks 0D4B "inverse-limit stage projection"]
abbrev stageProjection (M : SeqRingMod.{u, u} A ρ) (n : ℕ) :
    inverseLimit A ρ M ⟶
      (ModuleCat.restrictScalars (DerivedLimit.limitProjection A ρ n)).obj
        (stage A ρ M n) :=
  limit.π (DerivedLimit.ringedModuleLimitTower A ρ M) (op n)

/-- The canonical base-change morphism
`Aₙ ⊗[lim Aₙ] lim Mₙ ⟶ Mₙ` induced by the inverse-limit projection. -/
@[stacks 0D4B "inverse-limit base-change comparison"]
noncomputable def inverseLimitBaseChangeComparison
    (M : SeqRingMod.{u, u} A ρ) (n : ℕ) :
    (ModuleCat.extendScalars (DerivedLimit.limitProjection A ρ n)).obj
        (inverseLimit A ρ M) ⟶ stage A ρ M n :=
  ((ModuleCat.extendRestrictScalarsAdj
      (DerivedLimit.limitProjection A ρ n)).homEquiv _ _).symm
    (stageProjection A ρ M n)

variable (M : SeqRingMod.{u, u} A ρ)
variable [∀ n, Module.Finite (A n) (stage A ρ M n)]
variable [∀ n, Module.Flat (A (n + 1)) (stage A ρ M (n + 1))]
variable [Module.Projective (A 0) (stage A ρ M 0)]

/-- Lemma 15.13.4 (1): the inverse limit of a compatible system of finite modules is finite when
the transition maps are surjective with locally nilpotent kernels, the positive stages are flat,
the initial stage is projective, and the successor base-change maps are bijective. -/
@[stacks 0D4B "(1), finiteness of the inverse-limit module"]
theorem inverseLimit_finite
    (h_surjective : ∀ n, Function.Surjective (ρ n))
    (h_locallyNilpotent : ∀ n, RingHom.ker (ρ n) ≤ nilradical (A (n + 1)))
    (h_baseChange : ∀ n, Function.Bijective (stageBaseChangeComparison A ρ M n)) :
    Module.Finite (DerivedLimit.limitRing A ρ) (inverseLimit A ρ M) := sorry

/-- Lemma 15.13.4 (2): under the hypotheses of part (1), the inverse-limit module is projective
over the inverse-limit ring. -/
@[stacks 0D4B "(2), projectivity of the inverse-limit module"]
theorem inverseLimit_projective
    (h_surjective : ∀ n, Function.Surjective (ρ n))
    (h_locallyNilpotent : ∀ n, RingHom.ker (ρ n) ≤ nilradical (A (n + 1)))
    (h_baseChange : ∀ n, Function.Bijective (stageBaseChangeComparison A ρ M n)) :
    Module.Projective (DerivedLimit.limitRing A ρ) (inverseLimit A ρ M) := sorry

/-- Lemma 15.13.4 (3): under the hypotheses of part (1), base change of the inverse-limit module
to every stage recovers that stage module. -/
@[stacks 0D4B "(3), base change of the inverse-limit module"]
theorem inverseLimitBaseChangeComparison_bijective
    (h_surjective : ∀ n, Function.Surjective (ρ n))
    (h_locallyNilpotent : ∀ n, RingHom.ker (ρ n) ≤ nilradical (A (n + 1)))
    (h_baseChange : ∀ n, Function.Bijective (stageBaseChangeComparison A ρ M n))
    (n : ℕ) :
    Function.Bijective (inverseLimitBaseChangeComparison A ρ M n) := sorry

end CategoryTheory.SequentialInverseSystem.ModuleSystem.FiniteProjectiveLimit

end
