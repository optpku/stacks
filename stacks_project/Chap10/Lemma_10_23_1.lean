/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.AtPrime
import StacksCheckRecall

/-!
# Detecting module properties at prime localizations

@stack 00HN
-/

@[expose] public section

universe u v w x

namespace LocalizedModule.AtPrime

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]
variable {M₂ : Type w} [AddCommGroup M₂] [Module R M₂]
variable {M₃ : Type x} [AddCommGroup M₃] [Module R M₃]

/- Lemma 10.23.1 (1): an element is zero if and only if it vanishes after localization at every
prime ideal, if and only if it vanishes after localization at every maximal ideal. -/
@[stacks 00HN "(1)"]
#check (eq_zero_tfae (R := R) (M := M) :
  ∀ x : M, List.TFAE [
    x = 0,
    ∀ (P : Ideal R) [P.IsPrime],
      LocalizedModule.mkLinearMap P.primeCompl M x = 0,
    ∀ (P : Ideal R) [P.IsMaximal],
      LocalizedModule.mkLinearMap P.primeCompl M x = 0])

/- Lemma 10.23.1 (2): a module is zero if and only if every prime localization is zero, if and
only if every maximal-ideal localization is zero. -/
@[stacks 00HN "(2)"]
#check (subsingleton_tfae (R := R) (M := M) :
  List.TFAE [
    Subsingleton M,
    ∀ (P : Ideal R) [P.IsPrime], Subsingleton (LocalizedModule.AtPrime P M),
    ∀ (P : Ideal R) [P.IsMaximal], Subsingleton (LocalizedModule.AtPrime P M)])

/- Lemma 10.23.1 (3): exactness of `M₁ ⟶ M₂ ⟶ M₃` is equivalent to exactness after
localization at every prime ideal, and also to exactness after localization at every maximal
ideal. -/
@[stacks 00HN "(3)"]
#check (exact_tfae (R := R) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) :
  ∀ (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃), List.TFAE [
    Function.Exact f g,
    ∀ (P : Ideal R) [P.IsPrime],
      Function.Exact (LocalizedModule.map P.primeCompl f)
        (LocalizedModule.map P.primeCompl g),
    ∀ (P : Ideal R) [P.IsMaximal],
      Function.Exact (LocalizedModule.map P.primeCompl f)
        (LocalizedModule.map P.primeCompl g)])

/- Lemma 10.23.1 (4): injectivity of a linear map is equivalent to injectivity after
localization at every prime ideal, and also after localization at every maximal ideal. -/
@[stacks 00HN "(4)"]
#check (injective_tfae (R := R) (M := M) (N := N) :
  ∀ f : M →ₗ[R] N, List.TFAE [
    Function.Injective f,
    ∀ (P : Ideal R) [P.IsPrime],
      Function.Injective (LocalizedModule.map P.primeCompl f),
    ∀ (P : Ideal R) [P.IsMaximal],
      Function.Injective (LocalizedModule.map P.primeCompl f)])

/- Lemma 10.23.1 (5): surjectivity of a linear map is equivalent to surjectivity after
localization at every prime ideal, and also after localization at every maximal ideal. -/
@[stacks 00HN "(5)"]
#check (surjective_tfae (R := R) (M := M) (N := N) :
  ∀ f : M →ₗ[R] N, List.TFAE [
    Function.Surjective f,
    ∀ (P : Ideal R) [P.IsPrime],
      Function.Surjective (LocalizedModule.map P.primeCompl f),
    ∀ (P : Ideal R) [P.IsMaximal],
      Function.Surjective (LocalizedModule.map P.primeCompl f)])

/- Lemma 10.23.1 (6): bijectivity of a linear map is equivalent to bijectivity after
localization at every prime ideal, and also after localization at every maximal ideal. -/
@[stacks 00HN "(6)"]
#check (bijective_tfae (R := R) (M := M) (N := N) :
  ∀ f : M →ₗ[R] N, List.TFAE [
    Function.Bijective f,
    ∀ (P : Ideal R) [P.IsPrime],
      Function.Bijective (LocalizedModule.map P.primeCompl f),
    ∀ (P : Ideal R) [P.IsMaximal],
      Function.Bijective (LocalizedModule.map P.primeCompl f)])

end LocalizedModule.AtPrime

#check @element_zero_localization_tfae
#check @module_zero_localization_tfae
#check @injective_localization_tfae
#check @surjective_localization_tfae
#check @bijective_localization_tfae
