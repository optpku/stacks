/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.PNat.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.Sections

/-!
# Counterexamples for sections on affine ideal complements

This file records concrete failures of surjectivity for the canonical comparison from ideal-power
Hom colimits to sections of a tilde module on an ideal complement.
-/

@[expose] public section

open MvPolynomial

universe u

namespace AlgebraicGeometry.Scheme.Modules

namespace idealPowerHomColimitToComplementSections

/-- For the quotient of `k[x, y, z₁, z₂, ...]` by the relations `x ^ n * zₙ`, the canonical
comparison from the Hom colimit of powers of `(x)` to sections on its complement is not
surjective. -/
theorem notSurjective_countablePower
    (k : Type u) [Field k] :
    let A₀ : Type u := MvPolynomial (Bool ⊕ ℕ+) k
    let x₀ : A₀ := X (Sum.inl false)
    let J : Ideal A₀ := Ideal.span (Set.range fun n : ℕ+ ↦ x₀ ^ (n : ℕ) * X (Sum.inr n))
    let A : Type u := A₀ ⧸ J
    let x : A := Ideal.Quotient.mk J x₀
    let I : Ideal A := Ideal.span ({x} : Set A)
    ¬ Function.Surjective
      (idealPowerHomColimitToComplementSections
        I
        (Submodule.fg_span_singleton x)
        (ModuleCat.of A A)).hom := sorry

/-- For the quotient of `k[f, g, x, y, {aₙ, bₙ}]` by the relations `f * y - g * x` and
`aₙ * f ^ n + bₙ * g ^ n`, the canonical comparison from the Hom colimit of powers of `(f, g)`
to sections on its complement is not surjective. -/
theorem notSurjective_gluedFraction
    (k : Type u) [Field k] :
    let A₀ : Type u := MvPolynomial (Fin 4 ⊕ (Bool × ℕ+)) k
    let f₀ : A₀ := X (Sum.inl 0)
    let g₀ : A₀ := X (Sum.inl 1)
    let x₀ : A₀ := X (Sum.inl 2)
    let y₀ : A₀ := X (Sum.inl 3)
    let fg : Fin 2 → A₀ := Fin.cases f₀ fun _ ↦ g₀
    let J : Ideal A₀ :=
      Ideal.span <|
        ({f₀ * y₀ - g₀ * x₀} :
          Set A₀) ∪
          Set.range
            (fun n : ℕ+ ↦ X (Sum.inr (false, n)) * f₀ ^ (n : ℕ) +
              X (Sum.inr (true, n)) * g₀ ^ (n : ℕ))
    let A : Type u := A₀ ⧸ J
    let f : A := Ideal.Quotient.mk J f₀
    let g : A := Ideal.Quotient.mk J g₀
    let I : Ideal A := Ideal.span (Set.range fun i : Fin 2 ↦ Ideal.Quotient.mk J (fg i))
    ¬ Function.Surjective
      (idealPowerHomColimitToComplementSections
        I
        (Submodule.fg_span (Set.finite_range fun i : Fin 2 ↦ Ideal.Quotient.mk J (fg i)))
        (ModuleCat.of A A)).hom := sorry

end idealPowerHomColimitToComplementSections

end AlgebraicGeometry.Scheme.Modules
