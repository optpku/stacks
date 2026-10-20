/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Open
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.MorphismProperty
open AlgebraicGeometry

universe u

/- Lemma 29.23.2 (1): a locally finitely presented morphism that lifts generalizations is open. -/
@[stacks 01U1] #check (AlgebraicGeometry.isOpenMap_of_generalizingMap :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f],
    GeneralizingMap f → IsOpenMap f)

/- Lemma 29.23.2 (2): a locally finitely presented morphism that lifts generalizations after
every base change is universally open. -/
@[stacks 01U1] #check (AlgebraicGeometry.universallyOpen_of_universallyGeneralizing :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFinitePresentation f],
    (topologically GeneralizingMap).universally f → UniversallyOpen f)
