/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FppfRefinement

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/- Lemma 35.14.8 (1): flatness descends from `f ≫ g` to `g` when an fppf
cover of the intermediate scheme refines the singleton family containing `f`. -/
@[stacks 06NB] #check
  (AlgebraicGeometry.Flat.of_comp_of_fppf_refinement :
    ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      Flat (f ≫ g) → (𝒰 : FppfCover.{u, v} Y) →
        𝒰.presieve₀.FactorsThru (Presieve.singleton f) → Flat g)

/- Lemma 35.14.8 (2): local finite type descends from `f ≫ g` to `g` when an
fppf cover of the intermediate scheme refines the singleton family containing `f`. -/
@[stacks 06NB] #check
  (AlgebraicGeometry.LocallyOfFiniteType.of_comp_of_fppf_refinement :
    ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      LocallyOfFiniteType (f ≫ g) → (𝒰 : FppfCover.{u, v} Y) →
        𝒰.presieve₀.FactorsThru (Presieve.singleton f) → LocallyOfFiniteType g)

/- Lemma 35.14.8 (3): local finite presentation descends from `f ≫ g` to `g`
when an fppf cover of the intermediate scheme refines the singleton family containing `f`. -/
@[stacks 06NB] #check
  (AlgebraicGeometry.LocallyOfFinitePresentation.of_comp_of_fppf_refinement :
    ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      LocallyOfFinitePresentation (f ≫ g) → (𝒰 : FppfCover.{u, v} Y) →
        𝒰.presieve₀.FactorsThru (Presieve.singleton f) →
          LocallyOfFinitePresentation g)

end AlgebraicGeometry
