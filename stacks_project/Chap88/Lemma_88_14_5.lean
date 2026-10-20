/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.RigClosed.Jacobson
import StacksCheckRecall

/-!
# Contracting rig-closed primes along Jacobson special fibers
-/

@[expose] public section

universe u v

/- Lemma 88.14.5: let `φ : A →+* B` be an adic, topologically finite type
homomorphism of Noetherian adic rings, and let `q ⊂ B` be rig-closed. If
`A ⧸ I` is Jacobson for some ideal of definition `I ⊂ A`, then `q.comap φ`
is rig-closed in `A`. -/
@[stacks 0GGC] #check (Ideal.IsRigClosed.comap_of_isJacobsonRing :
    ∀ {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) (h_adic : φ.IsAdicHom) (h_tft : φ.TopologicallyOfFiniteType)
    (q : Ideal B) [q.IsRigClosed] (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    [IsJacobsonRing (A ⧸ I)],
    (q.comap φ).IsRigClosed)
