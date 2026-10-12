/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import stacks_project.Chap88.«88_2_0_2_TopologicallyFiniteType»
public import stacks_project.Chap88.«88_3_0_1»
public import stacks_project.Chap88.Lemma_88_3_1_Homotopy

/-!
# Lemma 88.3.1

The completed naive cotangent complex of an object of (88.2.0.2) is well
defined in the homotopy category of complexes of modules.
-/

@[expose] public section

open Algebra.NaiveCotangent.Adic
open HomotopyCategory

universe u

namespace Algebra.NaiveCotangent.Adic

variable {A B : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
variable (I : Ideal A) [Algebra.TopologicallyFiniteType I B]
variable {ι ι' : Type u} [Fintype ι] [Fintype ι']
variable (P : Presentation A B I ι) (Q : Presentation A B I ι')

/-- Lemma 88.3.1: Let `A` be a Noetherian ring and let `I ⊂ A` be an ideal.
Let `B` be an object of (88.2.0.2), i.e. an `I`-adically complete `A`-algebra
of topologically finite type. The completed naive cotangent complex
`NL_{B/A}^∧` is well defined in `K(B)`: for any two finite completed
polynomial presentations, the associated two-term complexes
`naiveCotangent I P` and `naiveCotangent I Q` are homotopy equivalent. -/
@[stacks 0GAE]
theorem naiveCotangent_homotopyEquiv :
    Nonempty (HomotopyEquiv (naiveCotangent I P) (naiveCotangent I Q)) :=
  sorry

/-- Well-definedness of `NL_{B/A}^∧` in `K(B)` as an isomorphism of the images
of two presentation complexes under `HomotopyCategory.quotient`. -/
theorem naiveCotangent_iso :
    Nonempty
      ((quotient (ModuleCat B) (ComplexShape.down ℕ)).obj (naiveCotangent I P) ≅
        (quotient (ModuleCat B) (ComplexShape.down ℕ)).obj (naiveCotangent I Q)) :=
  sorry

end Algebra.NaiveCotangent.Adic
