module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Sites.Monoidal

/-!
# Monoidal module sheaves

This leaf exposes the monoidal structure on sheaves of modules induced by a
monoidal sheafification localization.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type w} [CommRing Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [((J.W : MorphismProperty (Cᵒᵖ ⥤ ModuleCat.{w} Λ))).IsMonoidal]

/-- The monoidal structure on sheaves of `Λ`-modules induced from the site-level monoidal
localization data. -/
instance moduleSheafMonoidalCategory :
    MonoidalCategory (Sheaf J (ModuleCat.{w} Λ)) :=
  Sheaf.monoidalCategory J (ModuleCat.{w} Λ)

end CategoryTheory.Sheaf
