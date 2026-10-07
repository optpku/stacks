module

public import ReasLib.CategoryTheory.Limits.Colimit.Concrete.Finite

/-!
# Comparing concrete filtered colimit cocones

Maps out of a concrete filtered colimit are injective when every target cocone leg is injective.
They are surjective when the target legs jointly cover the target point. These two independent
criteria combine into a reusable bijectivity test.
-/

@[expose] public section

open CategoryTheory

universe w vC uC vJ uJ

namespace CategoryTheory.Limits

variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C]

/-- A map from a colimit cocone to a cocone whose legs jointly cover its point is surjective on
underlying elements. This direction does not require filteredness or preservation by `U`. -/
theorem IsColimit.desc_surjective_of_jointly_surjective
    (U : C ⥤ Type w) (B : J ⥤ C) {c : Cocone B} (hc : IsColimit c)
    (s : Cocone B)
    (hcover : ∀ x : U.obj s.pt,
      ∃ (j : J) (y : U.obj (B.obj j)), U.map (s.ι.app j) y = x) :
    Function.Surjective (U.map (hc.desc s)) := sorry

/-- A map from a preserved filtered colimit cocone to a cocone with injective legs is injective
on underlying elements. -/
theorem IsColimit.desc_injective_of_ι_injective [IsFiltered J]
    (U : C ⥤ Type w) (B : J ⥤ C) {c : Cocone B} (hc : IsColimit c)
    [PreservesColimit B U] (s : Cocone B)
    (hinj : ∀ j, Function.Injective (U.map (s.ι.app j))) :
    Function.Injective (U.map (hc.desc s)) := sorry

/-- A map from a preserved filtered colimit cocone is bijective when the target cocone legs are
injective and jointly cover the target point. -/
theorem IsColimit.desc_bijective_of_ι_injective_of_jointly_surjective [IsFiltered J]
    (U : C ⥤ Type w) (B : J ⥤ C) {c : Cocone B} (hc : IsColimit c)
    [PreservesColimit B U] (s : Cocone B)
    (hinj : ∀ j, Function.Injective (U.map (s.ι.app j)))
    (hcover : ∀ x : U.obj s.pt,
      ∃ (j : J) (y : U.obj (B.obj j)), U.map (s.ι.app j) y = x) :
    Function.Bijective (U.map (hc.desc s)) := sorry

/-- The canonical colimit descent map is surjective when the target cocone legs jointly cover
its point. -/
theorem colimit.desc_surjective_of_jointly_surjective
    (U : C ⥤ Type w) (B : J ⥤ C) [HasColimit B] (s : Cocone B)
    (hcover : ∀ x : U.obj s.pt,
      ∃ (j : J) (y : U.obj (B.obj j)), U.map (s.ι.app j) y = x) :
    Function.Surjective (U.map (colimit.desc B s)) := sorry

/-- The canonical filtered-colimit descent map is injective when every target cocone leg is
injective. -/
theorem colimit.desc_injective_of_ι_injective [IsFiltered J]
    (U : C ⥤ Type w) (B : J ⥤ C) [HasColimit B] [PreservesColimit B U]
    (s : Cocone B) (hinj : ∀ j, Function.Injective (U.map (s.ι.app j))) :
    Function.Injective (U.map (colimit.desc B s)) := sorry

/-- The canonical filtered-colimit descent map is bijective when the target cocone legs are
injective and jointly cover the target point. -/
theorem colimit.desc_bijective_of_ι_injective_of_jointly_surjective [IsFiltered J]
    (U : C ⥤ Type w) (B : J ⥤ C) [HasColimit B] [PreservesColimit B U]
    (s : Cocone B) (hinj : ∀ j, Function.Injective (U.map (s.ι.app j)))
    (hcover : ∀ x : U.obj s.pt,
      ∃ (j : J) (y : U.obj (B.obj j)), U.map (s.ι.app j) y = x) :
    Function.Bijective (U.map (colimit.desc B s)) := sorry

end CategoryTheory.Limits
