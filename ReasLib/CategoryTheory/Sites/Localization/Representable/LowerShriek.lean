module

public import ReasLib.CategoryTheory.Sites.Localization.Representable

/-!
# Lower-shriek comparison for representable localization

This leaf compares the generic slice localization lower shriek with product by
the sheafified representable.  It depends on the representable-localization
comparison, but not on relocalization between two slice sites.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v

noncomputable section

namespace CategoryTheory.GrothendieckTopology.RepresentableLocalization

variable {C : Type u} [Category.{v} C]

variable {J : GrothendieckTopology C}
variable (U : C)
variable [∀ G : (Over U)ᵒᵖ ⥤ Type (max u v), (Over.forget U).op.HasLeftKanExtension G]
variable [HasWeakSheafify J (Type (max u v))]
variable (F : Sheaf J (Type (max u v)))

/-- The underlying map of the lower-shriek comparison respects the maps to the sheafified
representable at `U`. -/
theorem lowerShriekOverPullbackComparisonApp_comm :
    prod.lift
        (comparisonHom J U (F.over U))
        (((Over.forget U).sheafAdjunctionContinuous (Type (max u v))
          (J.over U) J).counit.app F) ≫
      ((Over.star (J.sheafifiedRepresentable U)).obj F).hom =
    ((comparison J U).obj
      ((J.overPullback (Type (max u v)) U).obj F)).hom := sorry

/-- The component of the comparison from localized lower shriek to the slice functor. -/
noncomputable def lowerShriekOverPullbackComparisonApp :
    (J.overPullback (Type (max u v)) U ⋙
        comparison J U).obj F ⟶
      (Over.star (J.sheafifiedRepresentable U)).obj F :=
  Over.homMk
    (prod.lift
      (comparisonHom J U (F.over U))
      (((Over.forget U).sheafAdjunctionContinuous (Type (max u v))
        (J.over U) J).counit.app F))
    (lowerShriekOverPullbackComparisonApp_comm (J := J) (U := U) (F := F))

/-- The lower-shriek comparison components are natural in the ambient sheaf. -/
theorem lowerShriekOverPullbackComparisonApp_naturality
    {F G : Sheaf J (Type (max u v))} (η : F ⟶ G) :
    (J.overPullback (Type (max u v)) U ⋙
      comparison J U).map η ≫
        lowerShriekOverPullbackComparisonApp (J := J) (U := U) G =
      lowerShriekOverPullbackComparisonApp (J := J) (U := U) F ≫
        (Over.star (J.sheafifiedRepresentable U)).map η := sorry

/-- The canonical comparison from localization lower shriek to product with the sheafified
representable, expressed by `Over.star`. -/
noncomputable def lowerShriekOverPullbackComparison :
    J.overPullback (Type (max u v)) U ⋙
        comparison J U ⟶
      Over.star (J.sheafifiedRepresentable U) :=
  NatTrans.mk
    (lowerShriekOverPullbackComparisonApp (J := J) (U := U))
    (fun {_ _} η ↦
      lowerShriekOverPullbackComparisonApp_naturality (J := J) (U := U) η)

/-- The lower-shriek comparison to the slice functor is invertible.  This remains a theorem,
rather than a global instance, so a deferred proof cannot silently construct inverse data. -/
theorem lowerShriekOverPullbackComparison_isIso :
    IsIso (lowerShriekOverPullbackComparison (J := J) U) := sorry

end CategoryTheory.GrothendieckTopology.RepresentableLocalization
