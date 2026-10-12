/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Coskeleton.Successor
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 0187

# Constructions of one-step matching extensions

The universal-property leaf owns the reusable `Extension` interface and representation transport.
This module gives the canonical pointwise-coskeleton producer. The unconditional existence theorem
remains proposition-valued; it does not conceal a public choice of concrete extension data.
-/

@[expose] public section

open CategoryTheory
open SimplexCategory.Truncated
open scoped Simplicial SimplexCategory.Truncated

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject.Truncated.matching.Extension

variable {C : Type u} [Category.{v} C]

/-- The pointwise one-step coskeleton, transported to an arbitrary chosen representation of its
matching-family presheaf. This is the canonical concrete producer when the relevant pointwise
right Kan extension is available. -/
@[stacks 0187 "matching extension from a pointwise coskeleton"]
noncomputable def ofPointwiseCoskeleton {n : ℕ}
    {U : SimplicialObject.Truncated C n} {T : C}
    (R : (FaceFamily.presheaf U).RepresentableBy T)
    [SimplicialObject.Truncated.Between.HasPointwiseCoskeleton U (n + 1)
      (Nat.le_succ n)] : Extension R :=
  (trunc.cosk.succ.extension n U).changeRepresentation R

/-- Every representation of the matching-family presheaf admits a one-step extension. -/
@[stacks 0187 "one-step extension existence from matching representability"]
theorem nonempty {n : ℕ} {U : SimplicialObject.Truncated C n} {T : C}
    (R : (FaceFamily.presheaf U).RepresentableBy T) :
    Nonempty (Extension R) := sorry

end CategoryTheory.SimplicialObject.Truncated.matching.Extension
