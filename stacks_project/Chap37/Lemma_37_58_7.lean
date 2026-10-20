/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.Relative.Composition
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 37.58.7: relative finite presentation of a quasicoherent module ascends along
a locally finitely presented morphism of base schemes. -/
@[stacks 09TC] #check
  (AlgebraicGeometry.Scheme.Modules.IsFinitePresentationOver.comp :
    ∀ {X Y S : Scheme.{u}} {f : X ⟶ Y} [LocallyOfFiniteType f]
      {F : X.Modules} [F.IsQuasicoherent],
      F.IsFinitePresentationOver f →
        ∀ (g : Y ⟶ S) [LocallyOfFinitePresentation g],
          F.IsFinitePresentationOver (f ≫ g))
