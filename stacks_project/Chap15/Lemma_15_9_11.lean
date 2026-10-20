/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Etale.FiniteProjectiveLift
import StacksCheckRecall

/-!
# Lemma 15.9.11

@stack 07M5
-/

@[expose] public section

universe u v

namespace Algebra

variable {A : Type u} [CommRing A]
variable (I : Ideal A)
variable {Pbar : Type v} [AddCommGroup Pbar] [Module (A ⧸ I) Pbar]

-- Lemma 15.9.11 (07M5): a finite projective module over `A ⧸ I` lifts etale-locally over `A`.
@[stacks 07M5]
#check
  (exists_etale_finite_projective_lift_of_finite_projective_quotient (A := A) I :
    Module.FiniteProjective (A ⧸ I) Pbar →
      ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Etale A A')
        (eIso : (A ⧸ I) ≃ₐ[A ⧸ I] (A' ⧸ Ideal.map (algebraMap A A') I))
        (P' : Type v) (_ : AddCommGroup P') (_ : Module A' P'),
        let J : Ideal A' := Ideal.map (algebraMap A A') I
        let Q : Type u := A' ⧸ J
        let _ : CommRing Q := inferInstance
        let _ : Module Q Pbar := Module.compHom Pbar eIso.symm.toRingHom
        ∃ _ : (P' ⧸ (J • (⊤ : Submodule A' P'))) ≃ₗ[Q] Pbar,
          Module.FiniteProjective A' P')

end Algebra
