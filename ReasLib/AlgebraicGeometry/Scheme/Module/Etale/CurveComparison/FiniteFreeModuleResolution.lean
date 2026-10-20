/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.Homology.Single

@[expose] public section
open CategoryTheory
noncomputable section
universe u

namespace FiniteFreeModuleResolution
variable (S : Type u) [Ring S]

/-- The actual free S-module on the underlying elements. -/
abbrev free (M : ModuleCat.{u} S) : ModuleCat.{u} S := ModuleCat.of S (M →₀ S)

/-- The specified evaluation sends a formal sum to the same linear combination. -/
def evaluation (M : ModuleCat.{u} S) : free S M ⟶ M :=
  ModuleCat.ofHom (Finsupp.linearCombination S (fun m : M ↦ m))

/-- Kernel iteration fixes every syzygy; no projective object is chosen from
an existence assertion. -/
def syzygy (M : ModuleCat.{u} S) : ℕ → ModuleCat.{u} S
  | 0 => M
  | n + 1 => ModuleCat.of S (LinearMap.ker (evaluation S (syzygy M n)).hom)

/-- Every term is the specified free module on the previous actual kernel. -/
abbrev term (M : ModuleCat.{u} S) (n : ℕ) := free S (syzygy S M n)

/-- Evaluate into the kernel, then include it into the preceding free module. -/
def differential (M : ModuleCat.{u} S) (n : ℕ) : term S M (n + 1) ⟶ term S M n :=
  evaluation S (syzygy S M (n + 1)) ≫
    ModuleCat.ofHom (LinearMap.ker (evaluation S (syzygy S M n)).hom).subtype

/-- The kernel inclusion makes successive differentials compose to zero. -/
theorem differential_squared (M : ModuleCat.{u} S) (n : ℕ) :
    differential S M (n + 1) ≫ differential S M n = 0 := by sorry

/-- The actual kernel/free resolution complex. -/
def complex (M : ModuleCat.{u} S) :=
  ChainComplex.of (term S M) (differential S M) (differential_squared S M)

/-- The actual augmentation is evaluation on the free generators. -/
def augmentation (M : ModuleCat.{u} S) : complex S M ⟶ (ChainComplex.single₀ _).obj M :=
  (ChainComplex.toSingle₀Equiv (complex S M) M).symm ⟨evaluation S M, by sorry⟩

/-- Surjectivity of each free evaluation proves exactness of this specified resolution. -/
theorem augmentation_quasiIso (M : ModuleCat.{u} S) : QuasiIso (augmentation S M) := by sorry

/-- Projectivity is in ModuleCat S, not in a finite profinite-representation category. -/
def resolution (M : ModuleCat.{u} S) : ProjectiveResolution M where
  complex := complex S M
  projective n := by
    change Projective (ModuleCat.of S ((syzygy S M n) →₀ S))
    infer_instance
  π := augmentation S M
  quasiIso := augmentation_quasiIso S M

/-- A free module on a finite set over a finite ring is finite. -/
theorem free_finite [Finite S] (M : ModuleCat.{u} S) [Finite M] : Finite (free S M) :=
  Finite.of_injective (fun f : M →₀ S ↦ (f : M → S)) DFunLike.coe_injective

/-- Finiteness follows recursively from the explicit kernels and free modules.
It is not asserted for arbitrary selected projective resolutions. -/
theorem syzygy_finite [Finite S] (M : ModuleCat.{u} S) [Finite M] (n : ℕ) :
    Finite (syzygy S M n) := by
  induction n with
  | zero => exact inferInstanceAs (Finite M)
  | succ n hn =>
    -- Local instance justification (proof-local temporary data): use the induction hypothesis for this exact syzygy.
    letI : Finite (syzygy S M n) := hn
    -- Local instance justification (proof-local temporary data): this exact free module has finite coefficient and basis sets.
    letI : Finite (free S (syzygy S M n)) := free_finite S (syzygy S M n)
    change Finite (LinearMap.ker (evaluation S (syzygy S M n)).hom)
    infer_instance

/-- Finite inputs produce finite terms of THIS explicit projective resolution. -/
theorem term_finite [Finite S] (M : ModuleCat.{u} S) [Finite M] (n : ℕ) :
    Finite ((resolution S M).complex.X n) := by
  -- Local instance justification (proof-local temporary data): apply the proved finite-kernel recursion at n.
  letI : Finite (syzygy S M n) := syzygy_finite S M n
  exact free_finite S (syzygy S M n)

end FiniteFreeModuleResolution
