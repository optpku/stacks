/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.LocalCohomology.FundamentalClass

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Hom.LocalCohomology

universe u

/- Lemma 36.6.13: the canonical fundamental-class map from the pushed-forward tensor of
`(Λ[c] conormalSheaf i)ᘁ` with `i^*ℱ` to degree-`c` local cohomology is functorial in the
quasicoherent module `ℱ`. -/
@[stacks 0G7T] #check
  (AlgebraicGeometry.Scheme.Hom.LocalCohomology.fundamentalClass :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) (c : ℕ) [IsClosedImmersion i]
      [Scheme.Hom.FinitePresentation i]
      [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)],
      sourceFunctor i c ⟶ functor i c)

end
