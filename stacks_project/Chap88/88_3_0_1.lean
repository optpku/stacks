/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent
public import ReasLib.RingTheory.AdicCompletion.TopologicallyFiniteType

@[expose] public section

open Algebra.NaiveCotangent.Adic
open CategoryTheory

universe u

namespace Algebra.NaiveCotangent.Adic

variable {A B ι : Type u} [CommRing A] [CommRing B] [Algebra A B] [Fintype ι]

/- 88.3.0.1: Let `A` be Noetherian, `I` an ideal, and `B` an `I`-adically
complete `A`-algebra whose special fiber `B / IB` is of finite type over `A / I`.
Choose a presentation `B = A[x_ι]^∧ / J` on finitely many variables.
For this presentation, the completed naive
cotangent complex `NL_{B/A}^∧` is the two-term complex
`(J / J² ⟶ ⊕ᵢ B dx_i)` in homological degrees `1` and `0`, with differential
given by completed partial derivatives. -/
@[stacks 0AJR] #check (Algebra.NaiveCotangent.Adic.naiveCotangent :
    ∀ {A B ι : Type u} [CommRing A] [CommRing B] [Algebra A B] [Fintype ι]
      (I : Ideal A) (P : Presentation A B I ι),
      ChainComplex (ModuleCat B) ℕ)

section SourceContext

variable [IsNoetherianRing A] (I : Ideal A) [Algebra.TopologicallyFiniteType I B]
variable (P : Presentation A B I ι)

#check (Algebra.NaiveCotangent.Adic.naiveCotangent I P : ChainComplex (ModuleCat B) ℕ)

end SourceContext

end Algebra.NaiveCotangent.Adic
