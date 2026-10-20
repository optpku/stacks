/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.DenseOpen
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 38.11.1: a finite-type quasicoherent module flat over a locally finitely
presented morphism is finitely presented if its restriction above a retrocompact,
scheme-theoretically dense open of the base is finitely presented. -/
@[stacks 081N] #check
  (AlgebraicGeometry.Scheme.Modules.IsFinitePresentation.of_restrict_of_flatOver :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
      (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
      (_ : flatOver F f) (U : S.Opens)
      (_ : IsRetrocompact (U : Set S))
      (_ : schemeTheoreticallyDense U)
      (_ : (F.restrict ((f ⁻¹ᵁ U).ι)).IsFinitePresentation),
      F.IsFinitePresentation)

end AlgebraicGeometry.Scheme.Modules
