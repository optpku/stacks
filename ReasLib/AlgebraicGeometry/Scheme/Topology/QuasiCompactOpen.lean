/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- There exist an affine scheme `S` and an affine open `U` such that no quasi-compact open
`V` is disjoint from `U` while `U ⊔ V` is dense in `S`. -/
theorem exists_affine_open_no_quasiCompact_disjoint_dense :
    ∃ (S : Scheme.{u}) (U : S.Opens),
      IsAffine S ∧ IsAffineOpen U ∧
        ¬ ∃ V : S.Opens,
            IsCompact (V : Set S) ∧ U ⊓ V = ⊥ ∧
              Dense ((U ⊔ V : S.Opens) : Set S) := sorry

/-- There exist an affine scheme `S` and a closed point `s` whose complement contains no
quasi-compact open that is dense in the complement. -/
theorem exists_affine_closedPoint_complement_no_quasiCompact_dense :
    ∃ (S : Scheme.{u}) (s : S),
      IsAffine S ∧ IsClosed ({s} : Set S) ∧
        ¬ ∃ V : S.Opens,
            IsCompact (V : Set S) ∧ s ∉ V ∧
              ({s} : Set S)ᶜ ⊆ closure (V : Set S) := sorry

end AlgebraicGeometry.Scheme
