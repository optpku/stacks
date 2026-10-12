/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.FilteredColimitExtension.ToModuleCat
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u v

namespace ModuleCat

/- Lemma 56.4.5: over a coherent ring, the filtered-colimit extension of a left exact
functor between finitely presented module categories is left exact. -/
@[stacks 0GP8] #check
  (ModuleCat.filteredColimitExtension_preservesFiniteLimits_of_coherent_toModuleCat :
    ∀ {A : Type u} [CommRing A] [IsCoherentRing A] {B : Type v} [Ring B]
    (F : (isFinitePresentation.{u, max u v} A).FullSubcategory ⥤
      (isFinitePresentation.{v, max u v} B).FullSubcategory)
    [PreservesFiniteLimits (F ⋙ (isFinitePresentation.{v, max u v} B).ι)]
    (F' : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B)
    (e : (isFinitePresentation.{u, max u v} A).ι ⋙ F' ≅
      F ⋙ (isFinitePresentation.{v, max u v} B).ι)
    [PreservesFilteredColimitsOfSize.{max u v, max u v} F'],
    PreservesFiniteLimits F')

end ModuleCat
