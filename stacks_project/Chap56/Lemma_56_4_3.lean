/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.FilteredColimitExtension.Additive
public import ReasLib.Algebra.Category.ModuleCat.FilteredColimitExtension.RightExact
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u v

namespace ModuleCat

/- Lemma 56.4.3 (1) -/
@[stacks 0GP6] #check (ModuleCat.fpFilteredColimitExtension_additive :
    ∀ {A : Type u} [Ring A] {B : Type v} [Ring B]
      (F : (ModuleCat.isFinitePresentation.{u, max u v} A).FullSubcategory ⥤
        (ModuleCat.isFinitePresentation.{v, max u v} B).FullSubcategory) [F.Additive]
      (F' : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B)
      (e : (ModuleCat.isFinitePresentation.{u, max u v} A).ι ⋙ F' ≅
        F ⋙ (ModuleCat.isFinitePresentation.{v, max u v} B).ι)
      [PreservesFilteredColimitsOfSize.{max u v, max u v} F'], F'.Additive)

/- Lemma 56.4.3 (2) -/
@[stacks 0GP6] #check (ModuleCat.fpFilteredColimitExtension_preservesCoproducts :
    ∀ {A : Type u} [Ring A] {B : Type v} [Ring B]
      (F : (ModuleCat.isFinitePresentation.{u, max u v} A).FullSubcategory ⥤
        (ModuleCat.isFinitePresentation.{v, max u v} B).FullSubcategory) [F.Additive]
      (F' : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B)
      (e : (ModuleCat.isFinitePresentation.{u, max u v} A).ι ⋙ F' ≅
        F ⋙ (ModuleCat.isFinitePresentation.{v, max u v} B).ι)
      [PreservesFilteredColimitsOfSize.{max u v, max u v} F']
      (J : Type (max u v)), PreservesColimitsOfShape (Discrete J) F')

/- Lemma 56.4.3 (3) -/
@[stacks 0GP6] #check (ModuleCat.fpFilteredColimitExtension_preservesFiniteColimits :
    ∀ {A : Type u} [Ring A] {B : Type v} [Ring B]
      (F : (ModuleCat.isFinitePresentation.{u, max u v} A).FullSubcategory ⥤
        (ModuleCat.isFinitePresentation.{v, max u v} B).FullSubcategory)
      [PreservesFiniteColimits F]
      (F' : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B)
      (e : (ModuleCat.isFinitePresentation.{u, max u v} A).ι ⋙ F' ≅
        F ⋙ (ModuleCat.isFinitePresentation.{v, max u v} B).ι)
      [PreservesFilteredColimitsOfSize.{max u v, max u v} F'],
      PreservesFiniteColimits F')

end ModuleCat
