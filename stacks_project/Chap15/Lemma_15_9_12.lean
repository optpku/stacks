/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.SymmetricAlgebra.Kaehler
import StacksCheckRecall

/-!
# Lemma 15.9.12

@stack 07EV

The canonical owner records the conormal sequence associated to a finite-free presentation of the
generators of a symmetric algebra. Its tensor factors use the library-facing order
`SymmetricAlgebra A M ⊗[A] -`.
-/

@[expose] public section

open scoped TensorProduct
open Algebra

universe u v

namespace SymmetricAlgebra

variable {A : Type u} [CommRing A]
variable {M : Type v} [AddCommMonoid M] [Module A M]
variable {m : ℕ}

-- Lemma 15.9.12 (1) (07EV): the conormal sequence for a finite-free presentation of `M`.
@[stacks 07EV]
#check
  (presentationConormalSequence_exact :
    (q : (Fin m →₀ A) →ₗ[A] M) → Function.Surjective q →
      let C := SymmetricAlgebra A M
      let i : q.ker →ₗ[A] (Fin m →₀ A) := q.ker.subtype
      let toKaehler : C ⊗[A] (Fin m →₀ A) →ₗ[C] Ω[C⁄A] :=
        (KaehlerDifferential.D A C).tensorProductTo ∘ₗ
          (SymmetricAlgebra.ι A M).baseChange C ∘ₗ q.baseChange C
      Function.Exact (i.baseChange C) toKaehler ∧ Function.Surjective toKaehler)

-- Lemma 15.9.12 (2) (07EV): the canonical identification of the Kahler differentials.
@[stacks 07EV]
#check
  (tensorToKaehler_bijective :
    Function.Bijective
      ((((KaehlerDifferential.D A (SymmetricAlgebra A M)).tensorProductTo).comp
        ((SymmetricAlgebra.ι A M).baseChange (SymmetricAlgebra A M))) :
          SymmetricAlgebra A M ⊗[A] M →ₗ[SymmetricAlgebra A M]
            Ω[SymmetricAlgebra A M⁄A]))

end SymmetricAlgebra
