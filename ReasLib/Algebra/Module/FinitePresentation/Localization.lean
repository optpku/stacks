/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finitely Presented Models of Localized Modules

This leaf records the reusable approximation statement that a module which is
finitely presented after localization is locally the localization of a finitely
presented source module.  It does not choose a model globally; the theorem
states the exact comparison map and localized linear equivalence needed by a
consumer.

@stack 05N6
-/

@[expose] public section

universe u v w x

namespace Module.FinitePresentation

variable {A : Type u} [CommRing A]
variable {N : Type v} [AddCommGroup N] [Module A N]

/-- Lemma 10.126.4 (2): a finitely presented localization of a module comes from a
finitely presented source model, with its localized comparison map specified
by the canonical `LocalizedModule.map`. -/
@[stacks 05N6 "finitely presented localized module model"]
theorem exists_model_of_localized (T : Submonoid A)
    [Module.FinitePresentation (Localization T) (LocalizedModule T N)] :
    ∃ (N' : Type u) (_ : AddCommGroup N') (_ : Module A N')
      (_ : Module.FinitePresentation A N')
      (f : N' →ₗ[A] N)
      (e : LocalizedModule T N' ≃ₗ[Localization T] LocalizedModule T N),
      e.toLinearMap = LocalizedModule.map T f := sorry

/-- Tag `05N6`: if the original module is finite, its finitely presented
localized model can be chosen with a surjective comparison map. -/
@[stacks 05N6 "surjective finitely presented localized module model"]
theorem exists_surjective_model_of_localized (T : Submonoid A)
    [Module.Finite A N]
    [Module.FinitePresentation (Localization T) (LocalizedModule T N)] :
    ∃ (N' : Type u) (_ : AddCommGroup N') (_ : Module A N')
      (_ : Module.FinitePresentation A N')
      (f : N' →ₗ[A] N) (_ : Function.Surjective f)
      (e : LocalizedModule T N' ≃ₗ[Localization T] LocalizedModule T N),
      e.toLinearMap = LocalizedModule.map T f := sorry

section IsLocalizedModule

variable {T : Submonoid A}
variable {Aₛ : Type w} [CommRing Aₛ] [Algebra A Aₛ] [IsLocalization T Aₛ]
variable {Nₛ : Type x} [AddCommGroup Nₛ] [Module A Nₛ]
variable [Module Aₛ Nₛ] [IsScalarTower A Aₛ Nₛ]

-- This is the canonical `Aₛ`-action on a canonical localized source; it is local to avoid
-- adding an arbitrary localization realization to global instance search.
noncomputable local instance localizedModuleTargetModule
    {P : Type*} [AddCommGroup P] [Module A P] :
    Module Aₛ (LocalizedModule T P) :=
  LocalizedModule.moduleOfIsLocalization ..

/-- Tag `05N6`: a finitely presented module over any chosen localization target
`Aₛ` has a finitely presented model over `A`. The `Aₛ`-action on the canonical
localized source is the named local canonical action
`LocalizedModule.moduleOfIsLocalization`. -/
@[stacks 05N6 "finitely presented arbitrary-localization model"]
theorem exists_model_of_isLocalizedModule
    (g : N →ₗ[A] Nₛ) [IsLocalizedModule T g]
    [Module.FinitePresentation Aₛ Nₛ] :
    ∃ (N' : Type u) (_ : AddCommGroup N') (_ : Module A N')
      (_ : Module.FinitePresentation A N')
      (f : N' →ₗ[A] N)
      (e : LocalizedModule T N' ≃ₗ[Aₛ] Nₛ),
      e.toLinearMap =
        IsLocalizedModule.mapExtendScalars T (LocalizedModule.mkLinearMap T N') g Aₛ f := sorry

end IsLocalizedModule

end Module.FinitePresentation
