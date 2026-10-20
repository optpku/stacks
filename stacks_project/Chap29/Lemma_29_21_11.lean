/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Cancellation
import StacksCheckRecall

/-!
# Lemma 29.21.11

Cancellation for morphisms locally of finite presentation and of finite presentation.

@stack 02FV
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Lemma 29.21.11 (1): local finite presentation cancels against a locally finite type
right factor. -/
@[stacks 02FV] #check
  (AlgebraicGeometry.LocallyOfFinitePresentation.of_comp :
    ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
      [LocallyOfFinitePresentation (f ≫ g)] [LocallyOfFiniteType g],
      LocallyOfFinitePresentation f)

/- Lemma 29.21.11 (2): finite presentation cancels against a locally finite type right factor
when the intermediate scheme is quasi-separated. -/
@[stacks 02FV] #check
  (AlgebraicGeometry.Scheme.Hom.FinitePresentation.of_comp_of_quasiSeparatedSpace :
    ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
      [Scheme.Hom.FinitePresentation (f ≫ g)] [LocallyOfFiniteType g] [QuasiSeparatedSpace Y],
      Scheme.Hom.FinitePresentation f)

end AlgebraicGeometry
