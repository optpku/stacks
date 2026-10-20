/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Operations
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 29.21.3: the composition of two morphisms which are locally of finite presentation
is locally of finite presentation, and the composition of two morphisms of finite presentation
is of finite presentation. -/
@[stacks 01TR] #check
  (AlgebraicGeometry.Scheme.Hom.FinitePresentation.comp :
    ∀ {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z},
      Scheme.Hom.FinitePresentation f → Scheme.Hom.FinitePresentation g →
        Scheme.Hom.FinitePresentation (f ≫ g))

/- The composition of locally finite-presentation morphisms is locally of finite presentation. -/
#check
  (AlgebraicGeometry.locallyOfFinitePresentation_comp :
    ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
      [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g],
      LocallyOfFinitePresentation (f ≫ g))
