/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.ProRealization
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

/- Lemma 52.15.3: for a Noetherian scheme `X` and ideal-sheaf data `I`, the functor from
`Scheme.CoherentFormalModules X I` to `Pro (Scheme.QCoh X)` is fully faithful. -/
@[stacks 0EIQ] #check (AlgebraicGeometry.Scheme.CoherentFormalModules.proFunctor_map_bijective :
  ∀ {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    (F G : CoherentFormalModules X I),
    Function.Bijective (fun f : F ⟶ G ↦ (CoherentFormalModules.proFunctor I).map f))
