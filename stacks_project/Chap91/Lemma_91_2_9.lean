/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap91.«91_2_0_1_Solution»
public import ReasLib.RingTheory.CompleteIntersection.Local.RingHom
import Mathlib.Tactic.CrossRefAttribute

/-!
# Existence of square-zero solutions for local complete intersection maps

If the structure map A → B is a local complete intersection, the standing
square-zero diagram 91.2.0.1 admits a solution.
-/

@[expose] public section

noncomputable section

universe u

open RingHom.SquareZeroExtension

namespace RingHom.SquareZeroExtension

variable {A' A : Type u} [CommRing A'] [CommRing A]
variable (π : A' →+* A) [π.IsSquareZeroExtension]
variable (B : Type u) [CommRing B] [Algebra A B]
variable {N : Type u} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
variable (c : KernelModule π →ₗ[A] N)

/-- Lemma 91.2.9 If algebraMap A B is a local complete intersection ring map,
then there exists a solution of 91.2.0.1. The standing square-zero data are
π : A' →+* A and c : KernelModule π →ₗ[A] N, and a solution is Solution π c. -/
@[stacks 08S6]
theorem exists_solution_of_isLocalCompleteIntersection
    [(algebraMap A B).IsLocalCompleteIntersection] :
    Nonempty (@Solution A' A _ _ B _ _ π _ _ _ _ _ c _) := sorry

end SquareZeroExtension

end RingHom
