/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Reduced
import StacksCheckRecall

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- Scheme reducedness is equivalent to local reducedness in the sense of ring properties. -/
@[deprecated isReduced_iff_hasRingPropertyLocally (since := "2026-08-16")]
alias isReduced_iff_hasRingPropertyLocally_isReduced := isReduced_iff_hasRingPropertyLocally

end AlgebraicGeometry.Scheme

/- Lemma 28.4.4: A scheme is reduced if and only if it is locally reduced. -/
@[stacks 01OS] #check
  (AlgebraicGeometry.Scheme.isReduced_iff_hasRingPropertyLocally :
    ∀ X : AlgebraicGeometry.Scheme.{u}, AlgebraicGeometry.IsReduced X ↔
      X.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ _root_.IsReduced A))
