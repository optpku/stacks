/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Descending etale algebras across localizations

This leaf owns the algebra-level form of etale descent along an arbitrary
localization.  The localized base ring stays explicit, so the output includes
the actual `Aₛ`-algebra equivalence needed by consumers rather than only an
existence claim up to an unspecified localization model.
-/

open scoped TensorProduct

universe u v w

namespace Algebra.Etale

/-- Lemma 10.143.3 (00U2), clause (10): an etale algebra over an arbitrary
localization `Aₛ` of `A` is the base change of an etale `A`-algebra. -/
@[stacks 00U2 "etale localization descent"]
theorem exists_model_of_localization
    {A : Type u} [CommRing A]
    (M : Submonoid A) {Aₛ : Type v} [CommRing Aₛ] [Algebra A Aₛ] [IsLocalization M Aₛ]
    (B' : Type w) [CommRing B'] [Algebra Aₛ B'] [Algebra.Etale Aₛ B'] :
    ∃ (B : Type w) (_ : CommRing B) (_ : Algebra A B) (_ : Algebra.Etale A B),
      Nonempty (B' ≃ₐ[Aₛ] Aₛ ⊗[A] B) := sorry

end Algebra.Etale
