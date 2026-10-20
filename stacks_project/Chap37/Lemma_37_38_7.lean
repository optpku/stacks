/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Cover.Smooth.EtaleRefinement

universe u v

/- Lemma 37.38.7: every smooth covering family of a scheme admits an étale covering
family refining it. -/
@[stacks 055V] #check
  (AlgebraicGeometry.Scheme.SmoothCovering.exists_etaleRefinement :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {ι : Type v}
      {family : ι → CategoryTheory.Over S},
      AlgebraicGeometry.Scheme.SmoothCovering family →
        ∃ 𝒱 : AlgebraicGeometry.Scheme.Cover.{u}
            AlgebraicGeometry.Scheme.etalePrecoverage S,
          CategoryTheory.SemiRepresentableFamily.Over.Refines 𝒱.toOverFamily
            (CategoryTheory.SemiRepresentableFamily.Over.ofArrows
              (fun i ↦ (family i).left) (fun i ↦ (family i).hom)))
