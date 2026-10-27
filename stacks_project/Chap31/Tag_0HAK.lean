/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Rank.Generic
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma (0HAK). A finite-type quasi-coherent module on an integral scheme has
finite generic rank r and is free of rank r on some nonempty open subscheme. -/
@[stacks 0HAK] #check
  (AlgebraicGeometry.Scheme.Modules.exists_nonempty_open_free_of_finiteType :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
      (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType],
      ∃ r : ℕ, AlgebraicGeometry.Scheme.Modules.genericRank F = (r : Cardinal.{u}) ∧
        ∃ U : X.Opens, Nonempty U ∧
          Nonempty (F.restrict U.ι ≅
            (SheafOfModules.free (ULift.{u} (Fin r)) : U.toScheme.Modules)))
