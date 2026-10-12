/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation
public import ReasLib.CategoryTheory.ObjectProperty.FilteredColimitRestriction

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u v w z

namespace ModuleCat

/-- A functor from finitely presented `A`-modules to a category with filtered colimits
of size `max u v` extends to all `A`-modules, preserving filtered colimits at that
fixed size, uniquely up to the unique natural isomorphism compatible with the
restriction isomorphism. -/
theorem existsUniqueFilteredColimitExtension
    {A : Type u} [Ring A] {B : Type w} [Category.{z} B]
    [HasFilteredColimitsOfSize.{max u v, max u v} B]
    (F : (isFinitePresentation.{u, max u v} A).FullSubcategory ⥤ B) :
    ∃ (F' : ModuleCat.{max u v} A ⥤ B)
      (eF' : (isFinitePresentation.{u, max u v} A).ι ⋙ F' ≅ F)
      (_ : PreservesFilteredColimitsOfSize.{max u v, max u v} F'),
      ∀ (G : ModuleCat.{max u v} A ⥤ B)
        (eG : (isFinitePresentation.{u, max u v} A).ι ⋙ G ≅ F),
        PreservesFilteredColimitsOfSize.{max u v, max u v} G →
          ∃! α : F' ≅ G,
            Functor.isoWhiskerLeft (isFinitePresentation.{u, max u v} A).ι α ≪≫ eG = eF' := sorry

/-- A functor from finitely presented `A`-modules to finitely presented `B`-modules
extends to all `A`-modules with values in all `B`-modules, preserving filtered
colimits of size `max u v`, uniquely up to the unique natural isomorphism compatible
with the restriction isomorphism. -/
theorem existsUniqueFilteredColimitExtensionToModuleCat
    {A : Type u} [Ring A] {B : Type v} [Ring B]
    (F : (isFinitePresentation.{u, max u v} A).FullSubcategory ⥤
      (isFinitePresentation.{v, max u v} B).FullSubcategory) :
    ∃ (F' : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B)
      (eF' : (isFinitePresentation.{u, max u v} A).ι ⋙ F' ≅
        F ⋙ (isFinitePresentation.{v, max u v} B).ι)
      (_ : PreservesFilteredColimitsOfSize.{max u v, max u v} F'),
      ∀ (G : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B)
        (eG : (isFinitePresentation.{u, max u v} A).ι ⋙ G ≅
          F ⋙ (isFinitePresentation.{v, max u v} B).ι),
        PreservesFilteredColimitsOfSize.{max u v, max u v} G →
          ∃! α : F' ≅ G,
            Functor.isoWhiskerLeft (isFinitePresentation.{u, max u v} A).ι α ≪≫ eG = eF' := sorry

end ModuleCat
