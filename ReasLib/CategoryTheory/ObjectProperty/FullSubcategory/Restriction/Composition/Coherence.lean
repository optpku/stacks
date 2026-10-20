module

public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Composition.Naturality
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Identity

/-!
# Coherence of full-subcategory restriction comparisons

The identity and composition comparisons for restriction satisfy the
associativity and unit laws of a pseudofunctorial construction.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.ObjectProperty.FullSubcategory.restrict.compIso

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]
variable {K : Type u₄} [Category.{v₄} K]
variable {P : ObjectProperty C} {Q : ObjectProperty D}
variable {R : ObjectProperty E} {S : ObjectProperty K}

/-- Restriction composition comparisons satisfy associativity coherence. -/
@[stacks 001D "associativity coherence for full-subcategory restriction"]
theorem associativity (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ K)
    (hF : P ≤ Q.inverseImage F) (hG : Q ≤ R.inverseImage G)
    (hH : R ≤ S.inverseImage H) :
    compIso (F ⋙ G) H (mapsToComp hF hG) hH ≪≫
        Functor.isoWhiskerRight (compIso F G hF hG) (restrict H hH) ≪≫
        Functor.associator (restrict F hF) (restrict G hG) (restrict H hH) =
      natIso (mapsToComp (mapsToComp hF hG) hH)
          (mapsToComp hF (mapsToComp hG hH))
          (Functor.associator F G H) ≪≫
        compIso F (G ⋙ H) hF (mapsToComp hG hH) ≪≫
        Functor.isoWhiskerLeft (restrict F hF) (compIso G H hG hH) := sorry

/-- Restriction identity and composition comparisons satisfy left unit
coherence. -/
@[stacks 001D "left unit coherence for full-subcategory restriction"]
theorem left_unit (F : C ⥤ D) (hF : P ≤ Q.inverseImage F) :
    compIso (𝟭 C) F (mapsToId P) hF ≪≫
        Functor.isoWhiskerRight (idIso P) (restrict F hF) ≪≫
        Functor.leftUnitor (restrict F hF) =
      natIso (mapsToComp (mapsToId P) hF) hF
        (Functor.leftUnitor F) := sorry

/-- Restriction identity and composition comparisons satisfy right unit
coherence. -/
@[stacks 001D "right unit coherence for full-subcategory restriction"]
theorem right_unit (F : C ⥤ D) (hF : P ≤ Q.inverseImage F) :
    compIso F (𝟭 D) hF (mapsToId Q) ≪≫
        Functor.isoWhiskerLeft (restrict F hF) (idIso Q) ≪≫
        Functor.rightUnitor (restrict F hF) =
      natIso (mapsToComp hF (mapsToId Q)) hF
        (Functor.rightUnitor F) := sorry

end CategoryTheory.ObjectProperty.FullSubcategory.restrict.compIso
