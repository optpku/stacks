/-
Copyright (c) 2026 ReasLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.ModelTheory.Definability
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-!
# Existential projection in finite products

The owner of first-order definability is Mathlib's `Set.Definable`, with its
language, structure, and parameter set retained. This lemma gives its projection
closure in the `Fin.snoc` form used by geometric o-minimal presentations.
It holds for every first-order structure; no order, field, topology, or
one-dimensional finiteness assumption is needed.
-/

namespace Set

variable {M : Type*} {L : FirstOrder.Language} [L.Structure M]
  {P : Set M} {n : ℕ} {A : Set (Fin (n + 1) → M)}

/-- Definable finite-product sets remain definable after forgetting the last
coordinate. This is Mathlib's finite projection theorem in existential form. -/
theorem Definable.snoc_projection (hA : P.Definable L A) :
    P.Definable L {x : Fin n → M | ∃ y : M, Fin.snoc x y ∈ A} := by
  have himage := hA.image_comp (Fin.castSucc : Fin n → Fin (n + 1))
  have heq : (fun z : Fin (n + 1) → M => z ∘ Fin.castSucc) '' A =
      {x : Fin n → M | ∃ y : M, Fin.snoc x y ∈ A} := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z (Fin.last n), ?_⟩
      have heta : Fin.snoc (z ∘ Fin.castSucc) (z (Fin.last n)) = z := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp
        · simp [Function.comp]
      rwa [heta]
    · rintro ⟨y, hy⟩
      refine ⟨Fin.snoc x y, hy, ?_⟩
      funext i
      simp [Function.comp]
  rwa [heq] at himage

end Set

end
