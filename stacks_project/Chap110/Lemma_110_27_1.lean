/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Topology.QuasiCompactOpen
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u

open AlgebraicGeometry
open scoped AlgebraicGeometry

/- Lemma 110.27.1 (1): there exist an affine scheme `S` and an affine open
`U ⊂ S` such that there is no quasi-compact open `V ⊂ S` with `U ⊓ V = ⊥`
and `U ⊔ V` dense in `S`. -/
@[stacks 086H] #check
  (AlgebraicGeometry.Scheme.exists_affine_open_no_quasiCompact_disjoint_dense :
    ∃ (S : Scheme.{u}) (U : S.Opens),
      IsAffine S ∧ IsAffineOpen U ∧
        ¬ ∃ V : S.Opens,
            IsCompact (V : Set S) ∧ U ⊓ V = ⊥ ∧
              Dense ((U ⊔ V : S.Opens) : Set S))

/- Lemma 110.27.1 (2): there exist an affine scheme `S` and a closed point
`s ∈ S` such that `S \ {s}` contains no quasi-compact open that is dense in
`S \ {s}`. -/
@[stacks 086H] #check
  (AlgebraicGeometry.Scheme.exists_affine_closedPoint_complement_no_quasiCompact_dense :
    ∃ (S : Scheme.{u}) (s : S),
      IsAffine S ∧ IsClosed ({s} : Set S) ∧
        ¬ ∃ V : S.Opens,
            IsCompact (V : Set S) ∧ s ∉ V ∧
              ({s} : Set S)ᶜ ⊆ closure (V : Set S))
