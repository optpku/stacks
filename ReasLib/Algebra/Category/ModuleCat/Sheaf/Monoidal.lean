/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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

variable (Λ)

/-- The canonical map from pointwise tensor of sections to sections of the sheaf
tensor. -/
def moduleTensorSectionHom
    (F G : Sheaf J (ModuleCat.{w} Λ)) (U : Cᵒᵖ) :
    F.1.obj U ⊗ G.1.obj U ⟶ (F ⊗ G).1.obj U :=
  ((sheafificationAdjunction J (ModuleCat.{w} Λ)).unit.app
        (F.1 ⊗ G.1)).app U ≫
    ((sheafToPresheaf J (ModuleCat.{w} Λ)).map
      ((Functor.Monoidal.μIso
            (presheafToSheaf J (ModuleCat.{w} Λ)) F.1 G.1).inv ≫
        ((sheafificationAdjunction J
              (ModuleCat.{w} Λ)).counit.app F ⊗ₘ
          (sheafificationAdjunction J
              (ModuleCat.{w} Λ)).counit.app G :
            (presheafToSheaf J (ModuleCat.{w} Λ)).obj F.1 ⊗
                (presheafToSheaf J (ModuleCat.{w} Λ)).obj G.1 ⟶
              F ⊗ G))).app U

end CategoryTheory.Sheaf
