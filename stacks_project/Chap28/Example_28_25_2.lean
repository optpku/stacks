/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.Sections.Counterexamples
import StacksCheckRecall

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Example 28.25.2 (1): for the ring
`A = k[x, y, z₁, z₂, ...]/(x ^ n * zₙ | n ≥ 1)` and the ideal `I = (x)`, the canonical map
`colim_n Hom_A(I ^ n, A) → Γ(Spec(A) \ V(I), Ã)` is not surjective. -/
@[stacks 01PN] #check
  (AlgebraicGeometry.Scheme.Modules.idealPowerHomColimitToComplementSections.notSurjective_countablePower :
    ∀ (k : Type u) [Field k],
      let A₀ : Type u := MvPolynomial (Bool ⊕ ℕ+) k
      let x₀ : A₀ := MvPolynomial.X (Sum.inl false)
      let J : Ideal A₀ :=
        Ideal.span (Set.range fun n : ℕ+ ↦ x₀ ^ (n : ℕ) * MvPolynomial.X (Sum.inr n))
      let A : Type u := A₀ ⧸ J
      let x : A := Ideal.Quotient.mk J x₀
      let I : Ideal A := Ideal.span ({x} : Set A)
      ¬ Function.Surjective
        (idealPowerHomColimitToComplementSections
          I
          (Submodule.fg_span_singleton x)
          (ModuleCat.of A A)).hom)

/- Example 28.25.2 (2): for the ring
`A = k[f, g, x, y, {aₙ, bₙ}]/(f * y - g * x, aₙ * f ^ n + bₙ * g ^ n)` and the ideal
`I = (f, g)`, the canonical map `colim_n Hom_A(I ^ n, A) → Γ(Spec(A) \ V(I), Ã)` is not
surjective. -/
@[stacks 01PN] #check
  (AlgebraicGeometry.Scheme.Modules.idealPowerHomColimitToComplementSections.notSurjective_gluedFraction :
    ∀ (k : Type u) [Field k],
      let A₀ : Type u := MvPolynomial (Fin 4 ⊕ (Bool × ℕ+)) k
      let f₀ : A₀ := MvPolynomial.X (Sum.inl 0)
      let g₀ : A₀ := MvPolynomial.X (Sum.inl 1)
      let x₀ : A₀ := MvPolynomial.X (Sum.inl 2)
      let y₀ : A₀ := MvPolynomial.X (Sum.inl 3)
      let fg : Fin 2 → A₀ := Fin.cases f₀ fun _ ↦ g₀
      let J : Ideal A₀ :=
        Ideal.span <|
          ({f₀ * y₀ - g₀ * x₀} :
            Set A₀) ∪
            Set.range
              (fun n : ℕ+ ↦ MvPolynomial.X (Sum.inr (false, n)) * f₀ ^ (n : ℕ) +
                MvPolynomial.X (Sum.inr (true, n)) * g₀ ^ (n : ℕ))
      let A : Type u := A₀ ⧸ J
      let f : A := Ideal.Quotient.mk J f₀
      let g : A := Ideal.Quotient.mk J g₀
      let I : Ideal A := Ideal.span (Set.range fun i : Fin 2 ↦ Ideal.Quotient.mk J (fg i))
      ¬ Function.Surjective
        (idealPowerHomColimitToComplementSections
          I
          (Submodule.fg_span (Set.finite_range fun i : Fin 2 ↦ Ideal.Quotient.mk J (fg i)))
          (ModuleCat.of A A)).hom)

end AlgebraicGeometry.Scheme.Modules
