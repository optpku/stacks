/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.FiniteFactorization
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 32.9.7: let `f : X ⟶ S` be finite, with `S` quasi-compact and quasi-separated.
Then `f` factors over `S` through a closed immersion `X ⟶ X'`, where `X' ⟶ S` is finite
and of finite presentation. -/
@[stacks 01ZK] #check
  (AlgebraicGeometry.Scheme.Hom.FinitePresentation.exists_finite_closedImmersion_factorization_of_isFinite :
    {X S : Scheme.{u}} → (f : X ⟶ S) → [IsFinite f] → [CompactSpace S] →
      [QuasiSeparatedSpace S] →
        (MorphismProperty.comp @IsClosedImmersion
          (@IsFinite ⊓ (@Scheme.Hom.FinitePresentation : MorphismProperty Scheme))) f)
