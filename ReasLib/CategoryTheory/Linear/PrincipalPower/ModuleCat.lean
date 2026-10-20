/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import ReasLib.Algebra.Module.IdealPower.Predicate
public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler.ShortExact
public import ReasLib.CategoryTheory.Linear.PrincipalPower
public import ReasLib.RingTheory.Ideal.Principal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Concrete principal-power towers of modules

This file gives concrete `ModuleCat` models for the categorical principal-power kernel and
quotient systems.  The stages are torsion submodules and module quotients, so downstream module
arguments can use elements without reopening the abstract kernel and cokernel constructions.

-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SequentialInverseSystem

universe u

namespace CategoryTheory.ModuleCat.PrincipalPower

variable {A : Type u} [CommRing A]

/-- The concrete submodule `f ^ n • M`. -/
@[stacks 0H33 "concrete principal-power submodule"]
abbrev submodule (f : A) (M : ModuleCat.{u} A) (n : ℕ) : Submodule A M :=
  principalPowerIdeal f n • (⊤ : Submodule A M)

/-- Consecutive principal-power submodules form a descending chain. -/
theorem submodule_step_le (f : A) (M : ModuleCat.{u} A) (n : ℕ) :
    submodule f M (n + 2) ≤ submodule f M (n + 1) := sorry

/-- The concrete quotient stage `M ⧸ f ^ (n + 1) • M`. -/
@[stacks 0H33 "concrete principal-power quotient stage"]
abbrev quotientStage (f : A) (M : ModuleCat.{u} A) (n : ℕ) : ModuleCat.{u} A :=
  ModuleCat.of A (M ⧸ submodule f M (n + 1))

/-- The quotient transition induced by the identity of `M`. -/
@[stacks 0H33 "concrete principal-power quotient transition"]
abbrev quotientStep (f : A) (M : ModuleCat.{u} A) (n : ℕ) :
    quotientStage f M (n + 1) ⟶ quotientStage f M n :=
  ModuleCat.ofHom <|
    Submodule.mapQ (submodule f M (n + 2)) (submodule f M (n + 1))
      (LinearMap.id : M →ₗ[A] M) (submodule_step_le f M n)

/-- The concrete inverse system `(M ⧸ f ^ (n + 1) • M)ₙ`. -/
@[stacks 0H33 "concrete principal-power quotient tower"]
abbrev quotientSystem (f : A) (M : ModuleCat.{u} A) :
    SequentialInverseSystem (ModuleCat.{u} A) :=
  Functor.ofOpSequence (quotientStep f M)

/-- The concrete submodule of elements annihilated by `f ^ n`. -/
@[stacks 0H33 "concrete principal-power torsion submodule"]
abbrev torsionSubmodule (f : A) (M : ModuleCat.{u} A) (n : ℕ) : Submodule A M :=
  Submodule.torsionBy A M (f ^ n)

/-- The concrete stage `M[f ^ (n + 1)]` of principal-power torsion. -/
@[stacks 0H33 "concrete principal-power torsion stage"]
abbrev torsionStage (f : A) (M : ModuleCat.{u} A) (n : ℕ) : ModuleCat.{u} A :=
  ModuleCat.of A (torsionSubmodule f M (n + 1))

/-- Multiplication by `f` carries the `(n + 2)`nd torsion stage into the `(n + 1)`st stage. -/
theorem torsion_smul_mem (f : A) (M : ModuleCat.{u} A) (n : ℕ)
    (x : torsionSubmodule f M (n + 2)) :
    f • x.1 ∈ torsionSubmodule f M (n + 1) := sorry

/-- The principal-power torsion transition induced by multiplication by `f`. -/
@[stacks 0H33 "concrete principal-power torsion transition"]
abbrev torsionStep (f : A) (M : ModuleCat.{u} A) (n : ℕ) :
    torsionStage f M (n + 1) ⟶ torsionStage f M n :=
  ModuleCat.ofHom <|
    LinearMap.codRestrict (torsionSubmodule f M (n + 1))
      (((f : A) • (LinearMap.id : M →ₗ[A] M)).domRestrict
        (torsionSubmodule f M (n + 2)))
      (torsion_smul_mem f M n)

/-- The concrete inverse system `(M[f ^ (n + 1)])ₙ`. -/
@[stacks 0H33 "concrete principal-power torsion tower"]
abbrev torsionSystem (f : A) (M : ModuleCat.{u} A) :
    SequentialInverseSystem (ModuleCat.{u} A) :=
  Functor.ofOpSequence (torsionStep f M)

/-- The concrete principal Tate module `lim (M[f ^ (n + 1)])ₙ`. -/
@[stacks 0H33 "concrete principal Tate module"]
abbrev tateModule (f : A) (M : ModuleCat.{u} A) : ModuleCat.{u} A :=
  limit (torsionSystem f M)

/-- The concrete principal-power quotient system is Mittag-Leffler. -/
@[stacks 0H33 "principal-power quotient tower is Mittag-Leffler"]
theorem quotientSystem_isMittagLeffler (f : A) (M : ModuleCat.{u} A) :
    IsMittagLeffler (quotientSystem f M) := sorry

/-- In a short exact row with principal-power quotient left term and torsion right term, the
middle system is Mittag-Leffler exactly when the torsion system is. -/
@[stacks 0H33 "principal-power short exact Mittag-Leffler criterion"]
theorem shortExact_middle_isMittagLeffler_iff_torsion
    (f : A) (M N : ModuleCat.{u} A) (B : SequentialInverseSystem (ModuleCat.{u} A))
    (ι : quotientSystem f M ⟶ B) (π : B ⟶ torsionSystem f N)
    (hzero : ι ≫ π = 0) (hShort : (ShortComplex.mk ι π hzero).ShortExact) :
    IsMittagLeffler B ↔ IsMittagLeffler (torsionSystem f N) := sorry

end CategoryTheory.ModuleCat.PrincipalPower
