/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.GenericPoints
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 35.25.4: An étale separated morphism which induces residue-field isomorphisms at
the generic points of its source and is injective on those generic points is an open immersion. -/
@[stacks 09NQ] #check
  (AlgebraicGeometry.IsOpenImmersion.of_etale_of_isSeparated_of_genericPoints :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [IsSeparated f],
      (∀ ξ : X, ξ ∈ genericPoints X → IsIso (f.residueFieldMap ξ)) →
      Set.InjOn f.base (genericPoints X) → IsOpenImmersion f)
