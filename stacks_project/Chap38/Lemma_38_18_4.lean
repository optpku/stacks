/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Purity.Flat

@[expose] public section

open CategoryTheory

universe u

/- Lemma 38.18.4: for a finite type morphism `f : X ⟶ S` and a finite type
quasi-coherent module `F` on `X` that is flat over `S`, relative purity is
equivalent to universal relative purity. -/
@[stacks 05L6] #check
  (AlgebraicGeometry.Scheme.Modules.IsPureOver.iff_universally_of_flatOver :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.Scheme.Hom.FiniteType f]
      (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType],
      AlgebraicGeometry.Scheme.Modules.flatOver F f →
        (F.IsPureOver f ↔ F.IsUniversallyPureOver f))
