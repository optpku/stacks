/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Uniform denominators for finite modules

This leaf packages the finite-generation argument that replaces elementwise
denominators after localization by one denominator for the whole module or
submodule.  It is independent of any torsion or Noetherian-ring application.
-/

universe u v w

namespace Module.Finite

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]
variable {N' : Type*} [AddCommMonoid N'] [Module R N']

/-- If a map from a finite module vanishes after localization, one element of
the localizing submonoid annihilates the whole map. -/
@[stacks 07FC "uniform denominator for a finite module map"]
theorem exists_smul_eq_zero_of_localization [Module.Finite R M]
    (S : Submonoid R) (f : N →ₗ[R] N') [IsLocalizedModule S f]
    (g : M →ₗ[R] N) (h : f.comp g = 0) :
    ∃ s : S, s • g = 0 := sorry

end Module.Finite

namespace Module.Finite

variable {R : Type u} [CommRing R]
variable {A : Type v} [CommRing A] [Algebra R A]
variable {M : Type w} [AddCommGroup M] [Module A M] [Module R M]
  [IsScalarTower R A M]

/-- If a module finite over an `R`-algebra vanishes at a prime of `R`, then it
vanishes after inverting one element outside that prime. -/
@[stacks 061Q "one denominator for a finite module"]
theorem exists_away_subsingleton_of_atPrime [Module.Finite A M]
    (p : Ideal R) [p.IsPrime]
    (h : Subsingleton (LocalizedModule p.primeCompl M)) :
    ∃ g : R, g ∉ p ∧ Subsingleton (LocalizedModule (.powers g) M) := sorry

end Module.Finite

namespace Submodule

open scoped Pointwise

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]

/-- A localized inclusion of a finite submodule can be cleared by one
denominator, for any model of the localized ambient module. -/
@[stacks 07FC "uniform denominator for a localized submodule inclusion"]
theorem exists_smul_le_of_localized₀_le
    (S : Submonoid R) (f : M →ₗ[R] N) [IsLocalizedModule S f]
    (P Q : Submodule R M) [Module.Finite R P]
    (h : P.localized₀ S f ≤ Q.localized₀ S f) :
    ∃ s : S, s • P ≤ Q := sorry

/-- For a finite submodule, inclusion after an arbitrary realization of
localization is equivalent to an inclusion after clearing one denominator. -/
@[stacks 07FC "finite localized submodule inclusion criterion"]
theorem localized₀_le_iff_exists_smul_le
    (S : Submonoid R) (f : M →ₗ[R] N) [IsLocalizedModule S f]
    (P Q : Submodule R M) [Module.Finite R P] :
    P.localized₀ S f ≤ Q.localized₀ S f ↔
      ∃ s : S, s • P ≤ Q := sorry

/-- A localized inclusion of a finite submodule in the canonical localized
module can be cleared by one denominator. -/
@[stacks 07FC "uniform denominator for canonical localized submodule inclusion"]
theorem exists_smul_le_of_localized_le
    (S : Submonoid R) (P Q : Submodule R M) [Module.Finite R P]
    (h : P.localized S ≤ Q.localized S) :
    ∃ s : S, s • P ≤ Q := sorry

/-- For a finite submodule, canonical localization reflects inclusion up to
multiplication by one element of the localizing submonoid. -/
@[stacks 07FC "finite submodule inclusion after localization"]
theorem localized_le_iff_exists_smul_le
    (S : Submonoid R) (P Q : Submodule R M) [Module.Finite R P] :
    P.localized S ≤ Q.localized S ↔
      ∃ s : S, s • P ≤ Q := sorry

end Submodule

namespace Submodule

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- For any realization of a module localization, finite generation over the
localized ring is witnessed by the localization of a finite source submodule. -/
@[stacks 05N6 "finite submodule with full localized model"]
theorem exists_finite_of_localized'_eq_top
    {T : Type*} [CommSemiring T] [Algebra R T] (S : Submonoid R)
    [IsLocalization S T] {N : Type w} [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] N) [IsLocalizedModule S f] [Module T N]
    [IsScalarTower R T N] [Module.Finite T N] :
    ∃ P : Submodule R M, Module.Finite R P ∧ P.localized' T S f = ⊤ := sorry

/-- If a module becomes finite after localization, then a finite submodule
already generates the whole canonical localized module. -/
@[stacks 05N6 "finite submodule with full localization"]
theorem exists_finite_of_localized_eq_top
    (S : Submonoid R) [Module.Finite (Localization S) (LocalizedModule S M)] :
    ∃ P : Submodule R M, Module.Finite R P ∧ P.localized S = ⊤ := sorry

end Submodule

namespace Module.Finite

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- A finite localized module admits an explicit finite source model, comparison
map, and localized linear equivalence. The data are exposed directly so users
need not reconstruct the source map from a chosen finite submodule. -/
@[stacks 05N6 "finite localized module model"]
theorem exists_model_of_localized (S : Submonoid R)
    [Module.Finite (Localization S) (LocalizedModule S M)] :
    ∃ (M' : Type v) (_ : AddCommGroup M') (_ : Module R M')
      (_ : Module.Finite R M') (f : M' →ₗ[R] M)
      (e : LocalizedModule S M' ≃ₗ[Localization S] LocalizedModule S M),
      e.toLinearMap = LocalizedModule.map S f := sorry

end Module.Finite

namespace LocalizedModule

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- A finite module that vanishes after localization at a multiplicative
subset also vanishes after inverting one element of that subset. -/
@[stacks 076A]
theorem exists_away_subsingleton [Module.Finite R M] (S : Submonoid R)
    (hM : Subsingleton (LocalizedModule S M)) :
    ∃ f ∈ S, Subsingleton (LocalizedModule.Away f M) := sorry

/-- If a principal localization at an element of a multiplicative subset
vanishes, then the localization at the whole subset vanishes. -/
theorem subsingleton_of_away_subsingleton (S : Submonoid R) {f : R} (hf : f ∈ S)
    (hfM : Subsingleton (LocalizedModule.Away f M)) :
    Subsingleton (LocalizedModule S M) := sorry

/-- A finite module vanishes after localization at a multiplicative subset if
and only if it vanishes after inverting one element of that subset. -/
theorem subsingleton_iff_exists_away_subsingleton [Module.Finite R M] (S : Submonoid R) :
    Subsingleton (LocalizedModule S M) ↔
      ∃ f ∈ S, Subsingleton (LocalizedModule.Away f M) := sorry

end LocalizedModule
