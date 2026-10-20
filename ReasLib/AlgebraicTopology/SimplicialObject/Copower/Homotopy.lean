/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.Functor.Index
public import ReasLib.AlgebraicTopology.SimplicialObject.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Homotopies induced by simplicial copower reindexing

A homotopy between maps of indexing simplicial sets induces a simplicial homotopy between the
corresponding copower reindexing maps. The component map reindexes coproduct summands by the
combinatorial homotopy and applies the matching degeneracy map to the copied simplicial object.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SimplicialObject.copower

variable {C : Type u} [Category.{v} C]
variable {K L : SSet.{w}} (X : SimplicialObject C)
variable [HasCopower K X]
variable [HasCopower L X]
variable {a b : K ⟶ L} (H : SSet.Homotopy a b)

namespace indexHom.homotopy

/-- The component of the copower homotopy induced by an indexing simplicial-set homotopy. -/
@[stacks 019O "component of the induced copower homotopy"]
noncomputable def app {n : ℕ} (i : Fin (n + 1)) :
    (SimplicialObject.copower K X).obj (op ⦋n⦌) ⟶
      (SimplicialObject.copower L X).obj (op ⦋n + 1⦌) :=
  Sigma.map' (H.toSimplicialObjectHomotopy.h i) (fun _ ↦ X.σ i)

/-- The initial face of the copower homotopy is the reindexing map induced by its second
endpoint. -/
@[stacks 019O "initial face law for the induced copower homotopy"]
theorem app_zero_comp_δ_zero (n : ℕ) :
    app X H (0 : Fin (n + 1)) ≫
        (SimplicialObject.copower L X).δ (0 : Fin (n + 2)) =
      (copower.indexHom X b).app (op ⦋n⦌) := sorry

/-- The final face of the copower homotopy is the reindexing map induced by its first
endpoint. -/
@[stacks 019O "final face law for the induced copower homotopy"]
theorem app_last_comp_δ_last (n : ℕ) :
    app X H (Fin.last n) ≫
        (SimplicialObject.copower L X).δ (Fin.last (n + 1)) =
      (copower.indexHom X a).app (op ⦋n⦌) := sorry

/-- The copower homotopy components satisfy the first nonadjacent face identity. -/
@[stacks 019O "first nonadjacent face law for the induced copower homotopy"]
theorem app_succ_comp_δ_castSucc_of_le {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i ≤ j.castSucc) :
    app X H j.succ ≫
        (SimplicialObject.copower L X).δ i.castSucc =
      (SimplicialObject.copower K X).δ i ≫ app X H j := sorry

/-- The copower homotopy components satisfy the adjacent face identity. -/
@[stacks 019O "adjacent face law for the induced copower homotopy"]
theorem app_succ_comp_δ_castSucc_succ {n : ℕ}
    (j : Fin (n + 1)) :
    app X H j.succ ≫
        (SimplicialObject.copower L X).δ j.castSucc.succ =
      app X H j.castSucc ≫
        (SimplicialObject.copower L X).δ j.castSucc.succ := sorry

/-- The copower homotopy components satisfy the second nonadjacent face identity. -/
@[stacks 019O "second nonadjacent face law for the induced copower homotopy"]
theorem app_castSucc_comp_δ_succ_of_lt {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 1)) (hji : j.castSucc < i) :
    app X H j.castSucc ≫
        (SimplicialObject.copower L X).δ i.succ =
      (SimplicialObject.copower K X).δ i ≫ app X H j := sorry

/-- The copower homotopy components satisfy the first degeneracy identity. -/
@[stacks 019O "first degeneracy law for the induced copower homotopy"]
theorem app_comp_σ_castSucc_of_le {n : ℕ}
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    app X H j ≫
        (SimplicialObject.copower L X).σ i.castSucc =
      (SimplicialObject.copower K X).σ i ≫ app X H j.succ := sorry

/-- The copower homotopy components satisfy the second degeneracy identity. -/
@[stacks 019O "second degeneracy law for the induced copower homotopy"]
theorem app_comp_σ_succ_of_le {n : ℕ}
    (i j : Fin (n + 1)) (hji : j ≤ i) :
    app X H j ≫
        (SimplicialObject.copower L X).σ i.succ =
      (SimplicialObject.copower K X).σ i ≫ app X H j.castSucc := sorry

end indexHom.homotopy

/-- A simplicial-set homotopy induces a structured simplicial homotopy between the corresponding
copower reindexing maps. -/
@[stacks 019O "copower reindexing preserves simplicial homotopies"]
noncomputable def indexHom.homotopy :
    SimplicialObject.Homotopy (copower.indexHom X a) (copower.indexHom X b) where
  h := indexHom.homotopy.app X H
  h_zero_comp_δ_zero := indexHom.homotopy.app_zero_comp_δ_zero X H
  h_last_comp_δ_last := indexHom.homotopy.app_last_comp_δ_last X H
  h_succ_comp_δ_castSucc_of_lt := indexHom.homotopy.app_succ_comp_δ_castSucc_of_le X H
  h_succ_comp_δ_castSucc_succ := indexHom.homotopy.app_succ_comp_δ_castSucc_succ X H
  h_castSucc_comp_δ_succ_of_lt := indexHom.homotopy.app_castSucc_comp_δ_succ_of_lt X H
  h_comp_σ_castSucc_of_le := indexHom.homotopy.app_comp_σ_castSucc_of_le X H
  h_comp_σ_succ_of_lt := indexHom.homotopy.app_comp_σ_succ_of_le X H

end CategoryTheory.SimplicialObject.copower
