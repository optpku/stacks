/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Detecting module properties at prime localizations

This file packages the local-global results from Mathlib into direct `iff` interfaces for
localization at every prime or every maximal ideal. The six `List.TFAE` declarations give compact
equivalence families, while downstream arguments can use the finer `iff` API.
-/

@[expose] public section

universe u v w x

namespace LocalizedModule.AtPrime

variable {R : Type u} [CommSemiring R]

section Element

variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- An element is zero exactly when its image is zero after localization at every prime ideal. -/
@[stacks 00HN "(1), all primes"]
theorem eq_zero_iff_forall_prime (x : M) :
    x = 0 ↔ ∀ (P : Ideal R) [P.IsPrime],
      LocalizedModule.mkLinearMap P.primeCompl M x = 0 := by
  constructor
  · rintro rfl P _
    exact map_zero _
  · intro h
    exact Module.eq_zero_of_localization_maximal
      (fun P _ ↦ LocalizedModule.AtPrime P M)
      (fun P _ ↦ LocalizedModule.mkLinearMap P.primeCompl M) x (fun P _ ↦ h P)

/-- An element is zero exactly when its image is zero after localization at every maximal
ideal. -/
@[stacks 00HN "(1), all maximal ideals"]
theorem eq_zero_iff_forall_maximal (x : M) :
    x = 0 ↔ ∀ (P : Ideal R) [P.IsMaximal],
      LocalizedModule.mkLinearMap P.primeCompl M x = 0 := by
  constructor
  · rintro rfl P _
    exact map_zero _
  · intro h
    exact Module.eq_zero_of_localization_maximal
      (fun P _ ↦ LocalizedModule.AtPrime P M)
      (fun P _ ↦ LocalizedModule.mkLinearMap P.primeCompl M) x h

/-- Vanishing of an element can be checked after localization at every prime ideal, or only at
every maximal ideal. -/
@[stacks 00HN "(1)"]
theorem eq_zero_tfae (x : M) :
    List.TFAE [
      x = 0,
      ∀ (P : Ideal R) [P.IsPrime],
        LocalizedModule.mkLinearMap P.primeCompl M x = 0,
      ∀ (P : Ideal R) [P.IsMaximal],
        LocalizedModule.mkLinearMap P.primeCompl M x = 0
    ] := by
  rw [List.tfae_cons_cons, List.tfae_cons_cons]
  exact ⟨eq_zero_iff_forall_prime x,
    (eq_zero_iff_forall_prime x).symm.trans (eq_zero_iff_forall_maximal x),
    List.tfae_singleton _⟩

end Element

section Module

variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- A module is a subsingleton exactly when all of its prime localizations are
subsingletons. -/
@[stacks 00HN "(2), all primes"]
theorem subsingleton_iff_forall_prime :
    Subsingleton M ↔ ∀ (P : Ideal R) [P.IsPrime],
      Subsingleton (LocalizedModule.AtPrime P M) := by
  constructor
  · intro h P _
    letI : Subsingleton M := h
    exact IsLocalizedModule.subsingleton_of_subsingleton P.primeCompl
      (LocalizedModule.mkLinearMap P.primeCompl M)
  · intro h
    exact Module.subsingleton_of_localization_maximal
      (fun P _ ↦ LocalizedModule.AtPrime P M)
      (fun P _ ↦ LocalizedModule.mkLinearMap P.primeCompl M) (fun P _ ↦ h P)

/-- A module is a subsingleton exactly when all of its maximal-ideal localizations are
subsingletons. -/
@[stacks 00HN "(2), all maximal ideals"]
theorem subsingleton_iff_forall_maximal :
    Subsingleton M ↔ ∀ (P : Ideal R) [P.IsMaximal],
      Subsingleton (LocalizedModule.AtPrime P M) := by
  constructor
  · intro h P _
    letI : Subsingleton M := h
    exact IsLocalizedModule.subsingleton_of_subsingleton P.primeCompl
      (LocalizedModule.mkLinearMap P.primeCompl M)
  · intro h
    exact Module.subsingleton_of_localization_maximal
      (fun P _ ↦ LocalizedModule.AtPrime P M)
      (fun P _ ↦ LocalizedModule.mkLinearMap P.primeCompl M) h

/-- Being the zero module can be checked after localization at every prime ideal, or only at every
maximal ideal. -/
@[stacks 00HN "(2)"]
theorem subsingleton_tfae :
    List.TFAE [
      Subsingleton M,
      ∀ (P : Ideal R) [P.IsPrime], Subsingleton (LocalizedModule.AtPrime P M),
      ∀ (P : Ideal R) [P.IsMaximal], Subsingleton (LocalizedModule.AtPrime P M)
    ] := by
  rw [List.tfae_cons_cons, List.tfae_cons_cons]
  exact ⟨subsingleton_iff_forall_prime,
    subsingleton_iff_forall_prime.symm.trans subsingleton_iff_forall_maximal,
    List.tfae_singleton _⟩

end Module

section Exact

variable {M₁ : Type v} [AddCommMonoid M₁] [Module R M₁]
variable {M₂ : Type w} [AddCommMonoid M₂] [Module R M₂]
variable {M₃ : Type x} [AddCommMonoid M₃] [Module R M₃]

/-- Exactness of two linear maps is equivalent to exactness after localization at every prime
ideal. -/
@[stacks 00HN "(3), all primes"]
theorem exact_iff_forall_prime (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) :
    Function.Exact f g ↔ ∀ (P : Ideal R) [P.IsPrime],
      Function.Exact (LocalizedModule.map P.primeCompl f)
        (LocalizedModule.map P.primeCompl g) := by
  constructor
  · intro h P _
    exact LocalizedModule.map_exact P.primeCompl f g h
  · intro h
    exact exact_of_localized_maximal f g (fun P _ ↦ h P)

/-- Exactness of two linear maps is equivalent to exactness after localization at every maximal
ideal. -/
@[stacks 00HN "(3), all maximal ideals"]
theorem exact_iff_forall_maximal (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) :
    Function.Exact f g ↔ ∀ (P : Ideal R) [P.IsMaximal],
      Function.Exact (LocalizedModule.map P.primeCompl f)
        (LocalizedModule.map P.primeCompl g) := by
  constructor
  · intro h P _
    exact LocalizedModule.map_exact P.primeCompl f g h
  · exact exact_of_localized_maximal f g

/-- Exactness can be checked after localization at every prime ideal, or only at every maximal
ideal. -/
@[stacks 00HN "(3)"]
theorem exact_tfae (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) :
    List.TFAE [
      Function.Exact f g,
      ∀ (P : Ideal R) [P.IsPrime],
        Function.Exact (LocalizedModule.map P.primeCompl f)
          (LocalizedModule.map P.primeCompl g),
      ∀ (P : Ideal R) [P.IsMaximal],
        Function.Exact (LocalizedModule.map P.primeCompl f)
          (LocalizedModule.map P.primeCompl g)
    ] := by
  rw [List.tfae_cons_cons, List.tfae_cons_cons]
  exact ⟨exact_iff_forall_prime f g,
    (exact_iff_forall_prime f g).symm.trans (exact_iff_forall_maximal f g),
    List.tfae_singleton _⟩

end Exact

section Map

variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]

/-- A linear map is injective exactly when all of its prime localizations are injective. -/
@[stacks 00HN "(4), all primes"]
theorem injective_iff_forall_prime (f : M →ₗ[R] N) :
    Function.Injective f ↔ ∀ (P : Ideal R) [P.IsPrime],
      Function.Injective (LocalizedModule.map P.primeCompl f) := by
  constructor
  · intro h P _
    exact LocalizedModule.map_injective P.primeCompl f h
  · intro h
    exact injective_of_localized_maximal f (fun P _ ↦ h P)

/-- A linear map is injective exactly when all of its maximal-ideal localizations are
injective. -/
@[stacks 00HN "(4), all maximal ideals"]
theorem injective_iff_forall_maximal (f : M →ₗ[R] N) :
    Function.Injective f ↔ ∀ (P : Ideal R) [P.IsMaximal],
      Function.Injective (LocalizedModule.map P.primeCompl f) := by
  constructor
  · intro h P _
    exact LocalizedModule.map_injective P.primeCompl f h
  · exact injective_of_localized_maximal f

/-- Injectivity can be checked after localization at every prime ideal, or only at every maximal
ideal. -/
@[stacks 00HN "(4)"]
theorem injective_tfae (f : M →ₗ[R] N) :
    List.TFAE [
      Function.Injective f,
      ∀ (P : Ideal R) [P.IsPrime],
        Function.Injective (LocalizedModule.map P.primeCompl f),
      ∀ (P : Ideal R) [P.IsMaximal],
        Function.Injective (LocalizedModule.map P.primeCompl f)
    ] := by
  rw [List.tfae_cons_cons, List.tfae_cons_cons]
  exact ⟨injective_iff_forall_prime f,
    (injective_iff_forall_prime f).symm.trans (injective_iff_forall_maximal f),
    List.tfae_singleton _⟩

/-- A linear map is surjective exactly when all of its prime localizations are surjective. -/
@[stacks 00HN "(5), all primes"]
theorem surjective_iff_forall_prime (f : M →ₗ[R] N) :
    Function.Surjective f ↔ ∀ (P : Ideal R) [P.IsPrime],
      Function.Surjective (LocalizedModule.map P.primeCompl f) := by
  constructor
  · intro h P _
    exact LocalizedModule.map_surjective P.primeCompl f h
  · intro h
    exact surjective_of_localized_maximal f (fun P _ ↦ h P)

/-- A linear map is surjective exactly when all of its maximal-ideal localizations are
surjective. -/
@[stacks 00HN "(5), all maximal ideals"]
theorem surjective_iff_forall_maximal (f : M →ₗ[R] N) :
    Function.Surjective f ↔ ∀ (P : Ideal R) [P.IsMaximal],
      Function.Surjective (LocalizedModule.map P.primeCompl f) := by
  constructor
  · intro h P _
    exact LocalizedModule.map_surjective P.primeCompl f h
  · exact surjective_of_localized_maximal f

/-- Surjectivity can be checked after localization at every prime ideal, or only at every maximal
ideal. -/
@[stacks 00HN "(5)"]
theorem surjective_tfae (f : M →ₗ[R] N) :
    List.TFAE [
      Function.Surjective f,
      ∀ (P : Ideal R) [P.IsPrime],
        Function.Surjective (LocalizedModule.map P.primeCompl f),
      ∀ (P : Ideal R) [P.IsMaximal],
        Function.Surjective (LocalizedModule.map P.primeCompl f)
    ] := by
  rw [List.tfae_cons_cons, List.tfae_cons_cons]
  exact ⟨surjective_iff_forall_prime f,
    (surjective_iff_forall_prime f).symm.trans (surjective_iff_forall_maximal f),
    List.tfae_singleton _⟩

/-- A linear map is bijective exactly when all of its prime localizations are bijective. -/
@[stacks 00HN "(6), all primes"]
theorem bijective_iff_forall_prime (f : M →ₗ[R] N) :
    Function.Bijective f ↔ ∀ (P : Ideal R) [P.IsPrime],
      Function.Bijective (LocalizedModule.map P.primeCompl f) := by
  constructor
  · intro h P _
    exact ⟨LocalizedModule.map_injective P.primeCompl f h.1,
      LocalizedModule.map_surjective P.primeCompl f h.2⟩
  · intro h
    exact bijective_of_localized_maximal f (fun P _ ↦ h P)

/-- A linear map is bijective exactly when all of its maximal-ideal localizations are
bijective. -/
@[stacks 00HN "(6), all maximal ideals"]
theorem bijective_iff_forall_maximal (f : M →ₗ[R] N) :
    Function.Bijective f ↔ ∀ (P : Ideal R) [P.IsMaximal],
      Function.Bijective (LocalizedModule.map P.primeCompl f) := by
  constructor
  · intro h P _
    exact ⟨LocalizedModule.map_injective P.primeCompl f h.1,
      LocalizedModule.map_surjective P.primeCompl f h.2⟩
  · exact bijective_of_localized_maximal f

/-- Bijectivity can be checked after localization at every prime ideal, or only at every maximal
ideal. -/
@[stacks 00HN "(6)"]
theorem bijective_tfae (f : M →ₗ[R] N) :
    List.TFAE [
      Function.Bijective f,
      ∀ (P : Ideal R) [P.IsPrime],
        Function.Bijective (LocalizedModule.map P.primeCompl f),
      ∀ (P : Ideal R) [P.IsMaximal],
        Function.Bijective (LocalizedModule.map P.primeCompl f)
    ] := by
  rw [List.tfae_cons_cons, List.tfae_cons_cons]
  exact ⟨bijective_iff_forall_prime f,
    (bijective_iff_forall_prime f).symm.trans (bijective_iff_forall_maximal f),
    List.tfae_singleton _⟩

end Map

end LocalizedModule.AtPrime

section Compatibility

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]

/-- Vanishing of an element is equivalent to vanishing in all prime and maximal-ideal
localizations. -/
theorem element_zero_localization_tfae (x : M) :
    List.TFAE [
      x = 0,
      ∀ (P : Ideal R) [P.IsPrime],
        LocalizedModule.mkLinearMap P.primeCompl M x = 0,
      ∀ (P : Ideal R) [P.IsMaximal],
        LocalizedModule.mkLinearMap P.primeCompl M x = 0
    ] := by
  exact LocalizedModule.AtPrime.eq_zero_tfae x

/-- A module is zero exactly when all of its prime and maximal-ideal localizations are zero. -/
theorem module_zero_localization_tfae :
    List.TFAE [
      Subsingleton M,
      ∀ (P : Ideal R) [P.IsPrime], Subsingleton (LocalizedModule.AtPrime P M),
      ∀ (P : Ideal R) [P.IsMaximal], Subsingleton (LocalizedModule.AtPrime P M)
    ] := by
  exact LocalizedModule.AtPrime.subsingleton_tfae

/-- Injectivity of a linear map is equivalent to injectivity of all its prime and maximal-ideal
localizations. -/
theorem injective_localization_tfae (f : M →ₗ[R] N) :
    List.TFAE [
      Function.Injective f,
      ∀ (P : Ideal R) [P.IsPrime],
        Function.Injective (LocalizedModule.map P.primeCompl f),
      ∀ (P : Ideal R) [P.IsMaximal],
        Function.Injective (LocalizedModule.map P.primeCompl f)
    ] := by
  exact LocalizedModule.AtPrime.injective_tfae f

/-- Surjectivity of a linear map is equivalent to surjectivity of all its prime and maximal-ideal
localizations. -/
theorem surjective_localization_tfae (f : M →ₗ[R] N) :
    List.TFAE [
      Function.Surjective f,
      ∀ (P : Ideal R) [P.IsPrime],
        Function.Surjective (LocalizedModule.map P.primeCompl f),
      ∀ (P : Ideal R) [P.IsMaximal],
        Function.Surjective (LocalizedModule.map P.primeCompl f)
    ] := by
  exact LocalizedModule.AtPrime.surjective_tfae f

/-- Bijectivity of a linear map is equivalent to bijectivity of all its prime and maximal-ideal
localizations. -/
theorem bijective_localization_tfae (f : M →ₗ[R] N) :
    List.TFAE [
      Function.Bijective f,
      ∀ (P : Ideal R) [P.IsPrime],
        Function.Bijective (LocalizedModule.map P.primeCompl f),
      ∀ (P : Ideal R) [P.IsMaximal],
        Function.Bijective (LocalizedModule.map P.primeCompl f)
    ] := by
  exact LocalizedModule.AtPrime.bijective_tfae f

end Compatibility
