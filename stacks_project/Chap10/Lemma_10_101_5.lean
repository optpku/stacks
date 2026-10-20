/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flatness.Nilpotent
import StacksCheckRecall

/-!
# Flatness descent across a nilpotent thickening

@stack 051J
-/

@[expose] public section

open scoped TensorProduct

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]

/-
Lemma 10.101.5 (051J): for an injective algebra map `R → R'`, a nilpotent
ideal `I`, and an `R`-module `M`, flatness of `M / IM` over `R / I` together
with flatness of `R' ⊗[R] M` over `R'` implies flatness of `M` over `R`.

The source proof iterates the contracted extended square. Its reusable
mathematical statement is the universe-polymorphic ReasLib owner below; the
contracted-square step itself is separately available from
`Module.Flat.ContractedSquare`.
-/
@[stacks 051J]
#check (Module.Flat.Nilpotent.of_injective_algebraMap :
  ∀ {I : Ideal R},
    IsNilpotent I →
    Function.Injective (algebraMap R S) →
    Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) →
    Module.Flat S (S ⊗[R] M) →
    Module.Flat R M)

end
