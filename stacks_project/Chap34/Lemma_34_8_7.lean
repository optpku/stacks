/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Cover.Ph.Stability
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits

universe u v

/- Lemma 34.8.7 (1): for a family of locally finite-type morphisms to a
scheme, being a ph covering is equivalent to admitting a refining ph-covering
family. -/
@[stacks 0ET9] #check
  (AlgebraicGeometry.phCovering_iff_exists_refinement :
    ∀ {T : AlgebraicGeometry.Scheme.{u}} {ι : Type v}
      (X : ι → AlgebraicGeometry.Scheme.{u}) (π : ∀ i, X i ⟶ T)
      (hπ : ∀ i, AlgebraicGeometry.LocallyOfFiniteType (π i)),
        AlgebraicGeometry.PhCovering X π ↔
          ∃ (κ : Type v) (Y : κ → AlgebraicGeometry.Scheme.{u})
            (φ : ∀ k, Y k ⟶ T),
              AlgebraicGeometry.PhCovering Y φ ∧
                SemiRepresentableFamily.Over.Refines
                  (SemiRepresentableFamily.Over.ofArrows Y φ)
                  (SemiRepresentableFamily.Over.ofArrows X π))

/- Lemma 34.8.7 (2): for a family of locally finite-type morphisms to a
scheme, being a ph covering is equivalent to the singleton family induced by
the coproduct morphism being a ph covering. -/
@[stacks 0ET9] #check
  (AlgebraicGeometry.phCovering_iff_coproductSingleton :
    ∀ {T : AlgebraicGeometry.Scheme.{u}} {ι : Type u}
      (X : ι → AlgebraicGeometry.Scheme.{u}) (π : ∀ i, X i ⟶ T)
      (hπ : ∀ i, AlgebraicGeometry.LocallyOfFiniteType (π i)),
        AlgebraicGeometry.PhCovering X π ↔
          AlgebraicGeometry.PhCovering
            (fun p ↦
              ((FormalCoproduct.Over.coproductSingleton
                (FormalCoproduct.ofArrows X π)).obj p).left)
            (fun p ↦
              ((FormalCoproduct.Over.coproductSingleton
                (FormalCoproduct.ofArrows X π)).obj p).hom))
