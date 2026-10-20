/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.ChangeIdeal
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 30.23.11: on a Noetherian scheme, coherent formal-module categories associated to
ideal sheaves with the same closed support are equivalent. -/
@[stacks 0EHR]
#check (AlgebraicGeometry.Scheme.CoherentFormalModules.nonemptyEquivalence_of_support_eq :
  ∀ {X : Scheme.{u}} [IsNoetherian X] (I J : X.IdealSheafData), I.support = J.support →
    Nonempty (Scheme.CoherentFormalModules X I ≌ Scheme.CoherentFormalModules X J))
