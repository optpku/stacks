/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Operations
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 29.20.12 (1): the composite of two locally quasi-finite morphisms is locally
quasi-finite, including the local finite-type condition. -/
@[stacks 01TL] #check
  (CategoryTheory.MorphismProperty.comp_mem
      (@AlgebraicGeometry.LocallyOfFiniteType ⊓
        @AlgebraicGeometry.LocallyQuasiFinite :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme) :
    ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      (AlgebraicGeometry.LocallyOfFiniteType f ∧
          AlgebraicGeometry.LocallyQuasiFinite f) →
        (AlgebraicGeometry.LocallyOfFiniteType g ∧
            AlgebraicGeometry.LocallyQuasiFinite g) →
          AlgebraicGeometry.LocallyOfFiniteType (f ≫ g) ∧
            AlgebraicGeometry.LocallyQuasiFinite (f ≫ g))

/- Lemma 29.20.12 (2): the composite of two quasi-finite morphisms is quasi-finite. -/
@[stacks 01TL] #check
  (AlgebraicGeometry.Scheme.Hom.QuasiFinite.comp :
    ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z},
      AlgebraicGeometry.Scheme.Hom.QuasiFinite f →
        AlgebraicGeometry.Scheme.Hom.QuasiFinite g →
          AlgebraicGeometry.Scheme.Hom.QuasiFinite (f ≫ g))
