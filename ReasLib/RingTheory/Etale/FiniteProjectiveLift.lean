module

public import Mathlib.RingTheory.Etale.Basic
public import ReasLib.RingTheory.Finiteness.Projective
import Mathlib.Tactic.CrossRefAttribute

/-!
# Etale-local lifting of finite projective modules

@stack 07M5

A finite projective module over a quotient lifts after an etale base change which leaves the
quotient unchanged.
-/

@[expose] public section

universe u v

namespace Algebra

variable {A : Type u} [CommRing A]
variable (I : Ideal A)
variable {Pbar : Type v} [AddCommGroup Pbar] [Module (A ⧸ I) Pbar]

/-- Lemma 15.9.11 (Stacks `07M5`): a finite projective `A ⧸ I`-module lifts to a finite
projective module after an etale base change which induces an equivalence on the closed fiber. -/
@[stacks 07M5]
theorem exists_etale_finite_projective_lift_of_finite_projective_quotient
    (hPbar : Module.FiniteProjective (A ⧸ I) Pbar) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Etale A A')
      (eIso : (A ⧸ I) ≃ₐ[A ⧸ I] (A' ⧸ Ideal.map (algebraMap A A') I))
      (P' : Type v) (_ : AddCommGroup P') (_ : Module A' P'),
      let J : Ideal A' := Ideal.map (algebraMap A A') I
      let Q : Type u := A' ⧸ J
      let _ : CommRing Q := inferInstance
      let _ : Module Q Pbar := Module.compHom Pbar eIso.symm.toRingHom
      ∃ _ : (P' ⧸ (J • (⊤ : Submodule A' P'))) ≃ₗ[Q] Pbar,
        Module.FiniteProjective A' P' := sorry

end Algebra
