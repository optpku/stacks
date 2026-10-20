/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Factorization
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 32.9.1: let `f : X ⟶ S` be locally of finite type, with `X` quasi-compact and
quasi-separated. Then `f` factors over `S` through an immersion `X ⟶ X'`, where
`X' ⟶ S` is of finite presentation. -/
@[stacks 01ZE] #check
  (AlgebraicGeometry.Scheme.Hom.FinitePresentation.exists_immersion_factorization_of_locallyOfFiniteType :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier],
      (MorphismProperty.comp @IsImmersion
        (@Scheme.Hom.FinitePresentation : MorphismProperty Scheme)) f)
