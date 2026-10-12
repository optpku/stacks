/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Linear-map properties in equivalence ladders

@stack 00DV

This leaf transports injectivity and surjectivity through a commuting square
whose vertical maps are linear equivalences.
-/

@[expose] public section

universe u v w x y

namespace LinearMap

variable {R : Type u} [Semiring R]
variable {A : Type v} [AddCommMonoid A] [Module R A]
variable {B : Type w} [AddCommMonoid B] [Module R B]
variable {A' : Type x} [AddCommMonoid A'] [Module R A']
variable {B' : Type y} [AddCommMonoid B'] [Module R B']

/-- Injectivity transfers to the bottom map of a commuting ladder of linear equivalences. -/
@[stacks 00DV "injectivity in a linear-equivalence ladder"]
theorem injective_of_ladder_linearEquiv
    {f : A →ₗ[R] B} {g : A' →ₗ[R] B'}
    {eA : A ≃ₗ[R] A'} {eB : B ≃ₗ[R] B'}
    (h : g ∘ₗ eA = eB ∘ₗ f) (hf : Function.Injective f) :
    Function.Injective g := by
  intro x y hxy
  apply eA.symm.injective
  apply hf
  apply eB.injective
  calc
    eB (f (eA.symm x)) = g x := by
      simpa [LinearMap.comp_apply] using
        (LinearMap.congr_fun h (eA.symm x)).symm
    _ = g y := hxy
    _ = eB (f (eA.symm y)) := by
      simpa [LinearMap.comp_apply] using LinearMap.congr_fun h (eA.symm y)

/-- Surjectivity transfers to the bottom map of a commuting ladder of linear equivalences. -/
@[stacks 00DV "surjectivity in a linear-equivalence ladder"]
theorem surjective_of_ladder_linearEquiv
    {f : A →ₗ[R] B} {g : A' →ₗ[R] B'}
    {eA : A ≃ₗ[R] A'} {eB : B ≃ₗ[R] B'}
    (h : g ∘ₗ eA = eB ∘ₗ f) (hf : Function.Surjective f) :
    Function.Surjective g := by
  intro y
  obtain ⟨x, hx⟩ := hf (eB.symm y)
  refine ⟨eA x, ?_⟩
  calc
    g (eA x) = eB (f x) := by
      simpa [LinearMap.comp_apply] using LinearMap.congr_fun h x
    _ = eB (eB.symm y) := by rw [hx]
    _ = y := eB.apply_symm_apply y

end LinearMap
