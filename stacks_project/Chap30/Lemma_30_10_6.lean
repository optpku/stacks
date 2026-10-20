/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Extension
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 30.10.6: let `X` be a locally Noetherian scheme. A morphism between the
restrictions of coherent modules `ℱ` and `𝒢` to an open `U` extends to `𝒢` from a
coherent submodule of `ℱ` that agrees with `ℱ` over `U`. -/
@[stacks 0FD0] #check
  (AlgebraicGeometry.Scheme.Modules.exists_coherentSubobject_extension_of_restrict_hom :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
      (ℱ 𝒢 : X.Modules) [ℱ.IsCoherent] [𝒢.IsCoherent]
      (U : X.Opens)
      (φ : ((Scheme.Modules.restrictFunctor U.ι).obj ℱ) ⟶
        ((Scheme.Modules.restrictFunctor U.ι).obj 𝒢)),
      ∃ (ℱ' : Subobject ℱ), ∃ (_ : ((ℱ' : X.Modules)).IsCoherent),
        ∃ (_ : IsIso ((Scheme.Modules.restrictFunctor U.ι).map ℱ'.arrow)),
          ∃ φ' : (ℱ' : X.Modules) ⟶ 𝒢,
            (Scheme.Modules.restrictFunctor U.ι).map φ' =
              (Scheme.Modules.restrictFunctor U.ι).map ℱ'.arrow ≫ φ)
