/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.FilteredColimitExtension
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u v w z

/- Lemma 56.2.1: a functor from finitely presented `A`-modules to a category with
filtered colimits of size `max u v` extends to all `A`-modules, preserving filtered
colimits at that fixed size, uniquely up to the unique natural isomorphism compatible
with the restriction isomorphism. -/
@[stacks 0GNJ] #check
  (ModuleCat.existsUniqueFilteredColimitExtension :
    ∀ {A : Type u} [Ring A] {B : Type w} [Category.{z} B]
    [HasFilteredColimitsOfSize.{max u v, max u v} B]
    (F : (ModuleCat.isFinitePresentation.{u, max u v} A).FullSubcategory ⥤ B),
    ∃ (F' : ModuleCat.{max u v} A ⥤ B)
      (eF' : (ModuleCat.isFinitePresentation.{u, max u v} A).ι ⋙ F' ≅ F)
      (_ : PreservesFilteredColimitsOfSize.{max u v, max u v} F'),
      ∀ (G : ModuleCat.{max u v} A ⥤ B)
        (eG : (ModuleCat.isFinitePresentation.{u, max u v} A).ι ⋙ G ≅ F),
        PreservesFilteredColimitsOfSize.{max u v, max u v} G →
          ∃! α : F' ≅ G,
            Functor.isoWhiskerLeft
              (ModuleCat.isFinitePresentation.{u, max u v} A).ι α ≪≫ eG = eF')
