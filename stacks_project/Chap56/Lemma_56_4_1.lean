/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.Algebra.Category.ModuleCat.FilteredColimitExtension
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u v

/- Lemma 56.4.1: a functor from finitely presented `A`-modules to finitely presented
`B`-modules extends to all `A`-modules as a functor to all `B`-modules, preserving
filtered colimits, uniquely up to the unique natural isomorphism compatible with
restriction. -/
@[stacks 0GP4] #check
  (ModuleCat.existsUniqueFilteredColimitExtensionToModuleCat :
    ∀ {A : Type u} [Ring A] {B : Type v} [Ring B]
      (F : (ModuleCat.isFinitePresentation.{u, max u v} A).FullSubcategory ⥤
        (ModuleCat.isFinitePresentation.{v, max u v} B).FullSubcategory),
      ∃ (F' : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B)
        (eF' : (ModuleCat.isFinitePresentation.{u, max u v} A).ι ⋙ F' ≅
          F ⋙ (ModuleCat.isFinitePresentation.{v, max u v} B).ι)
        (_ : PreservesFilteredColimitsOfSize.{max u v, max u v} F'),
        ∀ (G : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B)
          (eG : (ModuleCat.isFinitePresentation.{u, max u v} A).ι ⋙ G ≅
            F ⋙ (ModuleCat.isFinitePresentation.{v, max u v} B).ι),
          PreservesFilteredColimitsOfSize.{max u v, max u v} G →
            ∃! α : F' ≅ G,
              Functor.isoWhiskerLeft
                (ModuleCat.isFinitePresentation.{u, max u v} A).ι α ≪≫ eG = eF')
