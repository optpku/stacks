/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.ModuleSystem.BaseChange
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.ModuleSystem.Reindex
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Base-change computations for reindexed module systems

This leaf records transport of the canonical module base-change maps under an
order-isomorphic change of stages.  It is the generic owner; finite-module
specializations use the same maps through `Module.toSystem`.
-/

@[expose] public section

open scoped TensorProduct

universe u v x y z

noncomputable section

namespace Ring.DirectLimit.Algebra.Approximation.ModuleSystem

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S} {M : Type x} [AddCommGroup M] [_root_.Module S M]

/-- Reindexing pulls back a transition base-change map along the order
isomorphism. -/
@[simp, stacks 00R1 "reindexed directed module system"]
theorem reindex_transitionBaseChangeMap (A : ModuleSystem f M) {J : Type z}
    [Preorder J] (e : J ≃o A.index) {j k : J} (h : j ≤ k) :
    (A.reindex e).transitionBaseChangeMap h =
      A.transitionBaseChangeMap (e.monotone h) := sorry

/-- Reindexing pulls back the final base-change computation at each stage. -/
@[simp, stacks 00R1 "reindexed directed module system"]
theorem reindex_finalBaseChangeMap_tmul (A : ModuleSystem f M) {J : Type z}
    [Preorder J] (e : J ≃o A.index) (j : J) (s : S)
    (m : A.moduleStage (e j)) :
    let _ : Algebra ((A.reindex e).target j) S :=
      ((A.reindex e).toHom.targetToLimit j).toAlgebra
    (A.reindex e).finalBaseChangeMap j
        (s ⊗ₜ[(A.reindex e).target j] m) =
      s • A.moduleToLimit (e j) m := sorry

end Ring.DirectLimit.Algebra.Approximation.ModuleSystem
