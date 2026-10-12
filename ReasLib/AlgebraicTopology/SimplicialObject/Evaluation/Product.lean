/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Evaluation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Product evaluation

Pointlike mapping spaces are stable under the diagonal reindexing of a cosimplicial object.  The
statement is kept as a proposition-level bridge; the diagonal and the reindexed object are the
concrete data used by derived comparison arguments.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.CosimplicialObject.Pointlike

variable {C : Type u} [Category.{v} C]

/-- The diagonal reindexing of a pointlike cosimplicial object is pointlike in `C × C`. -/
@[stacks 08QC "diagonal pointlike cosimplicial object"]
theorem hasHomSpaces_diag (Ubullet : CosimplicialObject C)
    (hUbullet : HasHomSpaces Ubullet) :
    HasHomSpaces (Functor.mapCosimplicialObject (Functor.diag C) Ubullet) := sorry

end CategoryTheory.CosimplicialObject.Pointlike
