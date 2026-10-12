/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialSet.TrivialKanFibration
public import Mathlib.AlgebraicTopology.SimplicialObject.Coskeletal
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 01A6

# Coskeletal criteria for trivial Kan fibrations

Degreewise isomorphism and epimorphism hypotheses imply the boundary-inclusion right lifting
property between coskeletal simplicial sets.
-/

@[expose] public section

open CategoryTheory Opposite Simplicial

universe u

namespace SSet.modelCategoryQuillen.I.rlp.coskeletal

/-- 01A6 (Lemma 14.32.1), in canonical categorical form: a map between `n`-coskeletal simplicial
sets that is an isomorphism below degree `n` and an epimorphism in degree `n` is a trivial Kan
fibration. -/
@[stacks 01A6 "categorical degreewise criterion for trivial Kan fibrations"]
theorem ofIsIso {V U : SSet.{u}} (f : V ⟶ U) (n : ℕ)
    [∀ i : Fin n, IsIso (f.app (op ⦋(i : ℕ)⦌))]
    [Epi (f.app (op ⦋n⦌))] [V.IsCoskeletal n] [U.IsCoskeletal n] :
    I.rlp f := sorry

/-- The explicit-premise bridge to the canonical categorical coskeletal criterion. -/
@[stacks 01A6 "explicit categorical degreewise criterion for trivial Kan fibrations"]
theorem ofIsIso.explicit {V U : SSet.{u}} (f : V ⟶ U) (n : ℕ)
    (hbelow : ∀ i < n, IsIso (f.app (op ⦋i⦌)))
    (h_epi : Epi (f.app (op ⦋n⦌)))
    (hV : V.IsCoskeletal n) (hU : U.IsCoskeletal n) :
    I.rlp f := sorry

/-- 01A6 (Lemma 14.32.1), in canonical concrete form: between `n`-coskeletal simplicial sets,
bijectivity below degree `n` and surjectivity in degree `n` imply the trivial Kan lifting
property. -/
@[stacks 01A6 "degreewise criterion for trivial Kan fibrations"]
theorem ofBijective {V U : SSet.{u}} (f : V ⟶ U)
    (n : ℕ) [V.IsCoskeletal n] [U.IsCoskeletal n]
    (hbelow : ∀ i < n, Function.Bijective (f.app (op ⦋i⦌)))
    (hn : Function.Surjective (f.app (op ⦋n⦌))) :
    I.rlp f := sorry

/-- The explicit-premise bridge to the canonical concrete coskeletal criterion. -/
@[stacks 01A6 "explicit concrete degreewise criterion for trivial Kan fibrations"]
theorem ofBijective.explicit {V U : SSet.{u}} (f : V ⟶ U) (n : ℕ)
    (hbelow : ∀ i < n, Function.Bijective (f.app (op ⦋i⦌)))
    (hn : Function.Surjective (f.app (op ⦋n⦌)))
    (hV : V.IsCoskeletal n) (hU : U.IsCoskeletal n) :
    I.rlp f := sorry

end SSet.modelCategoryQuillen.I.rlp.coskeletal
