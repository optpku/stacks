/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedGraded.Cokernel.ArtinRees
import StacksCheckRecall

/-!
# Lemma 15.4.2: associated graded cokernels under perturbation

The explicit quotient construction and its degree-preserving
`Ideal.AssociatedGraded.ring I`-linear equivalence are owned by
`Ideal.AssociatedGraded.Cokernel`.

@stack 07VF
-/

@[expose] public section

open scoped Pointwise

universe u v w x

noncomputable section

namespace Ideal.AssociatedGraded.Cokernel

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable {L : Type v} [AddCommGroup L] [Module A L] [Module.Finite A L]
variable {M : Type w} [AddCommGroup M] [Module A M] [Module.Finite A M]
variable {N : Type x} [AddCommGroup N] [Module A N] [Module.Finite A N]

@[stacks 07VF "Lemma 15.4.2"]
#check fun (I : Ideal A) {c : ℕ} {f f' : L →ₗ[A] M} {g g' : M →ₗ[A] N}
    (hf : f.IsArtinReesBound I c) (hg : g.IsArtinReesBound I c)
    (hexact : Function.Exact f g)
    (hff' : LinearMap.range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    (hgg' : LinearMap.range (g' - g) ≤ I ^ (c + 1) • (⊤ : Submodule A N))
    (hI : I ≤ Ring.jacobson A) (hcomplex' : g'.comp f' = 0) ↦
  let _ := hI
  (equiv I hf hg hexact hff' hgg' hcomplex' :
    gradedModule I (N ⧸ LinearMap.range g) ≃ₗ[ring I]
      gradedModule I (N ⧸ LinearMap.range g'))

end Ideal.AssociatedGraded.Cokernel

-- Canonical construction and its degreewise action.
@[stacks 07VF "degreewise associated graded cokernel equivalence"]
#check @Ideal.AssociatedGraded.Cokernel.pieceEquiv

@[stacks 07VF "associated graded cokernel equivalence"]
#check @Ideal.AssociatedGraded.Cokernel.equiv

@[stacks 07VF "graded action of the associated graded cokernel equivalence"]
#check @Ideal.AssociatedGraded.Cokernel.equiv_lof
