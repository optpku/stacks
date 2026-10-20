/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.GlobalSections
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

/- Lemma 59.39.3 -/
@[stacks 0A3H] #check
  (AlgebraicGeometry.Scheme.Etale.restrictGlobalSection_bijective_of_flat_geometricallyConnected :
    ∀ {T S : Scheme.{u}} (f : T ⟶ S) [Flat f] [QuasiCompact f]
      [GeometricallyConnected f]
      (F : Sheaf S.smallEtaleTopology (Type (u + 1))),
      Function.Bijective (AlgebraicGeometry.Scheme.Etale.restrictGlobalSection f F))
