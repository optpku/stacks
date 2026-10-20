/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Projective
public import ReasLib.LinearAlgebra.LinearMap.EssentialSurjection

@[expose] public section

universe u v w x

/-- A linear map is a projective cover, also called a projective envelope, if its domain is
projective and it is an essential surjection. -/
def LinearMap.IsProjectiveCover
    {R : Type u} [Ring R] {P : Type v} [AddCommGroup P] [Module R P]
    {M : Type w} [AddCommGroup M] [Module R M] (f : P →ₗ[R] M) : Prop :=
  Module.Projective R P ∧ f.IsEssentialSurjection

namespace LinearMap.IsProjectiveCover

/-- Construct a projective cover from projectivity of the domain and essentiality of the
surjection. -/
def of {R : Type u} [Ring R] {P : Type v} [AddCommGroup P] [Module R P]
    {M : Type w} [AddCommGroup M] [Module R M] {f : P →ₗ[R] M}
    (projective : Module.Projective R P) (essentialSurjection : f.IsEssentialSurjection) :
    f.IsProjectiveCover :=
  ⟨projective, essentialSurjection⟩

/-- A linear map is a projective cover exactly when its domain is projective and the map is
an essential surjection. -/
theorem iff_projective_and_essentialSurjection
    {R : Type u} [Ring R] {P : Type v} [AddCommGroup P] [Module R P]
    {M : Type w} [AddCommGroup M] [Module R M] {f : P →ₗ[R] M} :
    f.IsProjectiveCover ↔ Module.Projective R P ∧ f.IsEssentialSurjection := sorry

/-- Two projective covers of the same module have linearly equivalent domains, compatibly
with their maps to the module. -/
theorem exists_linearEquiv
    {R : Type u} [Ring R]
    {P : Type v} [AddCommGroup P] [Module R P]
    {P' : Type w} [AddCommGroup P'] [Module R P']
    {M : Type x} [AddCommGroup M] [Module R M]
    {f : P →ₗ[R] M} {g : P' →ₗ[R] M}
    (hf : f.IsProjectiveCover) (hg : g.IsProjectiveCover) :
    ∃ e : P ≃ₗ[R] P', g.comp e.toLinearMap = f := sorry

end LinearMap.IsProjectiveCover
