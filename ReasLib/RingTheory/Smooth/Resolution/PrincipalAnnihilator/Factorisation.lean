/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.Torsion.Stability
public import ReasLib.RingTheory.Algebra.Quotient.PrincipalPower
public import ReasLib.RingTheory.Smooth.Factorization.BaseControl
public import ReasLib.RingTheory.Smooth.Standard.Element.Selected

/-!
# Principal-annihilator finite factorizations

The torsion-step quotient and its annihilator are owned by `Submodule.TorsionStep`
and `Module.torsionStepAnnihilator`. This leaf specializes finite base control to
that canonical ideal.
-/

@[expose] public section

universe u v w

namespace Algebra.PrincipalAnnihilator

variable {R : Type u} {A : Type v} {Λ : Type w}
variable [CommRing R] [CommRing A] [CommRing Λ]
variable [Algebra R A] [Algebra R Λ]

/-- A finite factorisation carrying the principal-annihilator containment
produced in the first principal desingularisation step. -/
@[stacks 07CR "principal-annihilator finite factorisation"]
abbrev Factorisation (π : R) (f : A →ₐ[R] Λ) :=
  AlgHom.Factorisation.Finite.BaseControl f
    (Module.torsionStepAnnihilator R R π)

namespace Factorisation

variable {π : R} {f : A →ₐ[R] Λ}

/-- The midpoint of a principal-annihilator factorisation. -/
abbrev mid (F : Factorisation π f) := F.base.mid

/-- The source map of a principal-annihilator factorisation. -/
noncomputable abbrev fromSource (F : Factorisation π f) : A →ₐ[R] F.mid :=
  F.base.fromSource

/-- The target map of a principal-annihilator factorisation. -/
noncomputable abbrev toTarget (F : Factorisation π f) : F.mid →ₐ[R] Λ :=
  F.base.toTarget

/-- Attach principal-annihilator control to a finite factorisation. -/
def of (F : AlgHom.Factorisation.Finite f)
    (singularIdeal_le :
      Ideal.map (algebraMap R F.mid) (Module.torsionStepAnnihilator R R π) ≤
        Algebra.singularIdeal R F.mid) : Factorisation π f :=
  AlgHom.Factorisation.Finite.BaseControl.of F singularIdeal_le

/-- The finite-presentation, triangle, and principal-annihilator properties
carried by the bundled factorisation. -/
theorem spec (F : Factorisation π f) :
    Algebra.FinitePresentation R F.mid ∧
      F.toTarget.comp F.fromSource = f ∧
      Ideal.map (algebraMap R F.mid) (Module.torsionStepAnnihilator R R π) ≤
        Algebra.singularIdeal R F.mid := sorry

/-- A chosen compatible section modulo `π ^ 4` produces a bundled
principal-annihilator factorisation. -/
theorem nonempty
    (π : R) [IsNoetherianRing R] (f : A →ₐ[R] Λ)
    (hπ : IsStrictlyStandard R (algebraMap R A π))
    (hAnnΛ : Module.IsTorsionStable Λ Λ (algebraMap R Λ π))
    (ρ : Algebra.PrincipalQuotient R A π 4 →ₐ[R ⧸ principalPowerIdeal π 4]
      R ⧸ principalPowerIdeal π 4)
    (hρ :
      (Algebra.ofId (R ⧸ principalPowerIdeal π 4)
        (Algebra.PrincipalQuotient R Λ π 4)).comp ρ =
        Algebra.PrincipalQuotient.map f π 4) :
    Nonempty (Factorisation π f) := sorry

/-- Lemma 16.7.1 (07CR): existence of a compatible section modulo `π ^ 4`
produces a principal-annihilator factorisation. -/
@[stacks 07CR]
theorem nonempty_of_exists
    (π : R) [IsNoetherianRing R] (f : A →ₐ[R] Λ)
    (hπ : IsStrictlyStandard R (algebraMap R A π))
    (hAnnΛ : Module.IsTorsionStable Λ Λ (algebraMap R Λ π))
    (hρ : ∃ ρ :
        Algebra.PrincipalQuotient R A π 4 →ₐ[R ⧸ principalPowerIdeal π 4]
          R ⧸ principalPowerIdeal π 4,
      (Algebra.ofId (R ⧸ principalPowerIdeal π 4)
        (Algebra.PrincipalQuotient R Λ π 4)).comp ρ =
        Algebra.PrincipalQuotient.map f π 4) :
    Nonempty (Factorisation π f) := sorry

end Factorisation

end Algebra.PrincipalAnnihilator
