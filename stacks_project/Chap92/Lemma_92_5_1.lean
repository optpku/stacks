/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.Lemma_92_5_1_Augmentation
public import Mathlib.AlgebraicTopology.SimplicialObject.Coskeletal
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.RingTheory.FiniteType
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite type of the next matching object

If a simplicial object of finite-type `A`-algebra maps to `B` is `n`-coskeletal and a trivial
Kan fibration to `B`, then the degree `n + 1` algebra is of finite type over `A`.
-/

@[expose] public section

open CategoryTheory
open Opposite
open SimplicialObject
open SSet.modelCategoryQuillen
open scoped Simplicial

universe u

namespace CommRingCat.Under

/-- Lemma 92.5.1. Let `A` be a Noetherian ring, and let `A ⟶ B` be a finite type ring map.
Let `n ≥ 0`, and let `P` be a simplicial object of the category of `A`-algebra maps `C ⟶ B`
such that `overAugmentation P` is a trivial Kan fibration of simplicial sets, `P.obj (op ⦋k⦌)`
is of finite type over `A` for all `k ≤ n`, and `P` is `n`-coskeletal as a simplicial object
of that category. Then `P.obj (op ⦋n + 1⦌)` is a finite type `A`-algebra. -/
@[stacks 08PW]
theorem finiteType_succ_of_isCoskeletal
    {A : CommRingCat.{u}} [IsNoetherianRing A] {B : Under A} [Algebra.FiniteType A B]
    {n : ℕ} (P : SimplicialObject (Over B)) [P.IsCoskeletal n]
    (h_finiteType : ∀ k ≤ n, Algebra.FiniteType A (P.obj (op ⦋k⦌)).left)
    (h_trivialKan : I.rlp (overAugmentation P)) :
    Algebra.FiniteType A (P.obj (op ⦋n + 1⦌)).left :=
  sorry

end CommRingCat.Under
