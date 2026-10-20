/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc.Cofinality

@[expose] public section

open CategoryTheory

universe u v

/- Lemma 34.9.15: if `R` is a nonzero ring, then no set-indexed family of fpqc
covers of `Spec R` is cofinal under refinement among all fpqc covers. -/
@[stacks 0BBK] #check
  (AlgebraicGeometry.FpqcCover.not_exists_smallCofinalFamily_of_spec :
    ∀ (R : Type u) [CommRing R] [Nontrivial R],
      ¬ ∃ (α : Type v)
          (A : α → AlgebraicGeometry.FpqcCover.{u, max u v + 1}
            (AlgebraicGeometry.Scheme.Spec.obj (Opposite.op (CommRingCat.of R)))),
        ∀ 𝒰 : AlgebraicGeometry.FpqcCover.{u, max u v + 1}
            (AlgebraicGeometry.Scheme.Spec.obj (Opposite.op (CommRingCat.of R))),
          ∃ a : α,
            CategoryTheory.SemiRepresentableFamily.Over.Refines
              (A a).toOverFamily 𝒰.toOverFamily)
