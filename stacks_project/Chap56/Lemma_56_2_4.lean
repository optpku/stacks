/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap56.Lemma_56_2_1
public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation.Coherent
public import ReasLib.Algebra.Category.ModuleCat.FilteredColimitExtension.Coherent
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u v w z

/- Lemma 56.2.4 -/
@[stacks 0GNM] #check (ModuleCat.filteredColimitExtension_additive_of_coherent :
    ∀ {A : Type u} [CommRing A] [IsCoherentRing A] {B : Type w} [Category.{z} B]
      [Preadditive B] [HasFiniteBiproducts B] [HasKernels B]
      [HasFilteredColimitsOfSize.{max u v, max u v} B]
      (F : (ModuleCat.isFinitePresentation.{u, max u v} A).FullSubcategory ⥤ B)
      [PreservesFiniteLimits F]
      (F' : ModuleCat.{max u v} A ⥤ B)
      [PreservesFilteredColimitsOfSize.{max u v, max u v} F']
      (eF' : (ModuleCat.isFinitePresentation.{u, max u v} A).ι ⋙ F' ≅ F)
      [∀ (J : Type (max u v)) [Category.{max u v} J] [IsFiltered J]
        [HasColimitsOfShape J B] {X Y : J ⥤ B} (f : X ⟶ Y),
        PreservesLimit (parallelPair f 0) (colim : (J ⥤ B) ⥤ B)], F'.Additive)

#check (ModuleCat.instHasFiniteLimits_isFinitePresentation_of_isCoherentRing :
    ∀ {A : Type u} [CommRing A] [IsCoherentRing A],
      HasFiniteLimits (ModuleCat.isFinitePresentation.{u, max u v} A).FullSubcategory)

#check (ModuleCat.filteredColimitExtension_preservesFiniteLimits_of_coherent :
    ∀ {A : Type u} [CommRing A] [IsCoherentRing A] {B : Type w} [Category.{z} B]
      [Preadditive B] [HasFiniteBiproducts B] [HasKernels B]
      [HasFilteredColimitsOfSize.{max u v, max u v} B]
      (F : (ModuleCat.isFinitePresentation.{u, max u v} A).FullSubcategory ⥤ B)
      [PreservesFiniteLimits F]
      (F' : ModuleCat.{max u v} A ⥤ B)
      [PreservesFilteredColimitsOfSize.{max u v, max u v} F']
      (eF' : (ModuleCat.isFinitePresentation.{u, max u v} A).ι ⋙ F' ≅ F)
      [∀ (J : Type (max u v)) [Category.{max u v} J] [IsFiltered J]
        [HasColimitsOfShape J B] {X Y : J ⥤ B} (f : X ⟶ Y),
        PreservesLimit (parallelPair f 0) (colim : (J ⥤ B) ⥤ B)],
      PreservesFiniteLimits F')

#check (ModuleCat.filteredColimitExtension_preservesCoproducts_of_coherent :
    ∀ {A : Type u} [CommRing A] [IsCoherentRing A] {B : Type w} [Category.{z} B]
      [Preadditive B] [HasFiniteBiproducts B] [HasKernels B]
      [HasFilteredColimitsOfSize.{max u v, max u v} B]
      (F : (ModuleCat.isFinitePresentation.{u, max u v} A).FullSubcategory ⥤ B)
      [PreservesFiniteLimits F]
      (F' : ModuleCat.{max u v} A ⥤ B)
      [PreservesFilteredColimitsOfSize.{max u v, max u v} F']
      (eF' : (ModuleCat.isFinitePresentation.{u, max u v} A).ι ⋙ F' ≅ F)
      [∀ (J : Type (max u v)) [Category.{max u v} J] [IsFiltered J]
        [HasColimitsOfShape J B] {X Y : J ⥤ B} (f : X ⟶ Y),
        PreservesLimit (parallelPair f 0) (colim : (J ⥤ B) ⥤ B)]
      (J : Type (max u v)), PreservesColimitsOfShape (Discrete J) F')
