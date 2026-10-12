/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap10.Lemma_10_127_13

/-!
@stack 00R6

Eventually flat stages in a directed local-hom approximation.
-/

@[expose] public section

universe uR uS uM

section

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
variable {f : R →+* S} [IsLocalHom f]
variable {M : Type uM} [AddCommGroup M] [_root_.Module S M]

namespace DirectedLocalHomApproximation.Module

/-- Chap10 Lemma 10 128 3

Stacks tag `00R6` (`lemma-colimit-eventually-flat`).

Let `R → S`, `M`, `Λ`, `R_λ → S_λ`, and `M_λ` be as in Lemma `10.127.13`.
Assume that `M` is flat over `R`. Then for some `λ ∈ Λ` the module `M_λ`
is flat over `R_λ`. This is the main source-facing declaration. -/
@[stacks 00R6]
theorem exists_flat_stage_of_flat
    (A : DirectedLocalHomApproximation.Module f M)
    (hflat :
      let _ : _root_.Module R M := _root_.Module.compHom M f
      _root_.Module.Flat R M) :
    ∃ i : A.Λ, _root_.Module.Flat (A.RStage i) (A.moduleStage i) := sorry

end DirectedLocalHomApproximation.Module

end
