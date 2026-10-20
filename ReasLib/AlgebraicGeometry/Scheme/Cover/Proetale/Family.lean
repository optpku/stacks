/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Proetale

/-!
# Indexed pro-étale covering families
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Scheme.Proetale

variable {T : Scheme.{u}} {ι : Type v}

/-- An indexed family of objects of `Over T` is pro-étale covering when its
arrows generate a presieve in the canonical pro-étale precoverage. -/
abbrev IsCovering (family : ι → Over T) : Prop :=
  CategoryTheory.Presieve.ofArrows (fun index ↦ (family index).left)
      (fun index ↦ (family index).hom) ∈ Scheme.proetalePrecoverage.coverings T

/-- The indexed pro-étale covering predicate is equivalent to weak étaleness
of every arrow together with finite affine refinements over affine target opens. -/
theorem isCovering_iff_finiteAffineRefinement (family : ι → Over T) :
    IsCovering family ↔
      (∀ index : ι, WeaklyEtale (family index).hom) ∧
        ∀ U : T.Opens, IsAffineOpen U →
          ∃ n : ℕ,
            ∃ a : Fin n → ι,
              ∃ V : (j : Fin n) → ((family (a j)).left).Opens,
                (∀ j : Fin n, IsAffineOpen (V j)) ∧
                  (⋃ j : Fin n,
                    (family (a j)).hom.base ''
                      (V j : Set (family (a j)).left.carrier)) =
                    (U : Set T.carrier) := sorry

end AlgebraicGeometry.Scheme.Proetale
