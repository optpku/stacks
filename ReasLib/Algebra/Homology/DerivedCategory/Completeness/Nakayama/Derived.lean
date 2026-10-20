/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.KoszulLimit.Nonpositive
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived Nakayama vanishing

A derived-complete object is detected by its derived reduction modulo a finitely generated ideal.
The statement is kept separate from the module-level Nakayama theorem and from the powered-Koszul
proof route.

@stack 0G1U
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped DerivedTensorProduct

universe u

namespace DerivedCategory.DerivedComplete

variable {A : Type u} [CommRing A]

/-- Lemma 15.92.20 (0G1U): if `I` is finitely generated, `K` is derived complete with respect to
`I`, and the derived reduction `K ⊗ᴸ_A (A ⧸ I)[0]` is zero, then `K` is zero. -/
@[stacks 0G1U]
theorem isZero_of_derivedTensor_quotient_isZero
    (I : Ideal A) (hI : I.FG) (K : DerivedCategory (ModuleCat.{u} A))
    (hK : K.IsDerivedCompleteWithRespectTo I)
    (hKI : IsZero
      (K ⊗[A]^L
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) (0 : ℤ)).obj
          (ModuleCat.of A (A ⧸ I)))) :
    IsZero K := sorry

end DerivedCategory.DerivedComplete
