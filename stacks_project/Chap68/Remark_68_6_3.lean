/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap68.Lemma_68_17_8
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty

namespace AlgebraicGeometry.AlgebraicSpace

section

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
  [QuasiCompact f] [Etale f] [Surjective f] [IsReasonable X]

/- Remark 68.6.3: reasonable algebraic spaces are technically easier to work with
than very reasonable ones. If `f : X ⟶ Y` is a quasi-compact étale surjective
morphism of algebraic spaces and `X` is reasonable, then so is `Y`. Descent of
the property “very reasonable” along such a morphism is not claimed. -/
@[stacks 03JY] #check (IsReasonable.of_quasiCompact_etale_surjective f : IsReasonable Y)

end

end AlgebraicGeometry.AlgebraicSpace
