/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.SeparatedFactorization
import StacksCheckRecall

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory

universe u

/- Proposition 32.9.6: let `f : X ⟶ S` be a morphism of schemes. Assume `f` is of finite type
and separated, and `S` is quasi-compact and quasi-separated. Then there exists a separated
morphism of finite presentation `f' : X' ⟶ S` and a closed immersion `X ⟶ X'` over `S`. -/
@[stacks 01ZJ] #check
  (AlgebraicGeometry.Scheme.Hom.FinitePresentation.exists_separated_closedImmersion_factorization_of_finiteType :
    {X S : Scheme.{u}} → (f : X ⟶ S) → [Scheme.Hom.FiniteType f] → [IsSeparated f] →
      [CompactSpace S] → [QuasiSeparatedSpace S] →
        (MorphismProperty.comp @IsClosedImmersion
          ((@Scheme.Hom.FinitePresentation : MorphismProperty Scheme) ⊓ @IsSeparated)) f)
