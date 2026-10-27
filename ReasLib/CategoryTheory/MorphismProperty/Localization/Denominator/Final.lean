/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Filtered.Final
public import ReasLib.CategoryTheory.MorphismProperty.Localization.Denominator.Comma
public import ReasLib.CategoryTheory.MorphismProperty.Localization.LeftFractionColimit
public import ReasLib.CategoryTheory.MorphismProperty.Localization.RightFractionColimit

/-!
# Finality of denominator comparison functors

For a left calculus of fractions, target denominators are cofinal in the costructured-arrow
indexing category of the localization.  The dual source-denominator functor is initial under a
right calculus of fractions.  These canonical instances let downstream colimit and limit code use
the standard `Functor.Final` and `Functor.Initial` APIs without local instance reconstruction.
-/

@[expose] public section

universe v u vD uD

namespace CategoryTheory.MorphismProperty

open Limits

variable {C : Type u} [Category.{v} C]
variable {D : Type uD} [Category.{vD} D]

namespace Under

private theorem denominators_isFiltered (S : MorphismProperty C)
    [S.HasLeftCalculusOfFractions] (X : C) :
    IsFiltered (MorphismProperty.Under S ⊤ X) where
  nonempty := ⟨MorphismProperty.Under.mk ⊤ (𝟙 X) (S.id_mem X)⟩
  cocone_objs U V := by
    obtain ⟨φ, hφ⟩ :=
      (RightFraction.mk U.hom U.prop V.hom).exists_leftFraction
    exact ⟨MorphismProperty.Under.mk ⊤ (V.hom ≫ φ.s)
      (S.comp_mem _ _ V.prop φ.hs),
      MorphismProperty.Under.homMk φ.f hφ.symm,
      MorphismProperty.Under.homMk φ.s rfl, trivial⟩
  cocone_maps {U V} f g := by
    obtain ⟨Z, t, ht, h⟩ := HasLeftCalculusOfFractions.ext f.right g.right
      U.hom U.prop ((MorphismProperty.Under.w f).trans (MorphismProperty.Under.w g).symm)
    exact ⟨MorphismProperty.Under.mk ⊤ (V.hom ≫ t)
      (S.comp_mem _ _ V.prop ht), MorphismProperty.Under.homMk t rfl,
      MorphismProperty.Under.Hom.ext h⟩

namespace toCostructuredArrow

/-- Every localization costructured arrow admits a morphism to a target-denominator stage. -/
theorem exists_hom (S : MorphismProperty C) [S.HasLeftCalculusOfFractions]
    {X : C} (Y : CostructuredArrow S.Q (S.Q.obj X)) :
    ∃ U : MorphismProperty.Under S ⊤ X,
      Nonempty (Y ⟶ (MorphismProperty.Under.toCostructuredArrow S X).obj U) := by
  obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction S.Q S Y.hom
  refine ⟨MorphismProperty.Under.mk ⊤ φ.s φ.hs,
    ⟨CategoryTheory.CostructuredArrow.homMk φ.f ?_⟩⟩
  change S.Q.map φ.f ≫ (Localization.isoOfHom S.Q S φ.s φ.hs).inv = Y.hom
  exact hφ.symm

/-- Parallel comparisons from a localization costructured arrow to one target-denominator stage
become equal after a further denominator refinement. -/
theorem exists_equalizer (S : MorphismProperty C) [S.HasLeftCalculusOfFractions]
    {X : C} {Y : CostructuredArrow S.Q (S.Q.obj X)}
    (U : MorphismProperty.Under S ⊤ X)
    (f g : Y ⟶ (MorphismProperty.Under.toCostructuredArrow S X).obj U) :
    ∃ (V : MorphismProperty.Under S ⊤ X) (h : U ⟶ V),
      f ≫ (MorphismProperty.Under.toCostructuredArrow S X).map h =
        g ≫ (MorphismProperty.Under.toCostructuredArrow S X).map h := by
  have hfg : S.Q.map f.left = S.Q.map g.left := by
    apply (cancel_mono (Localization.isoOfHom S.Q S U.hom U.prop).inv).1
    exact (CostructuredArrow.w f).trans (CostructuredArrow.w g).symm
  obtain ⟨Z, t, ht, h⟩ := (map_eq_iff_postcomp S.Q S f.left g.left).1 hfg
  refine ⟨MorphismProperty.Under.mk ⊤ (U.hom ≫ t)
    (S.comp_mem _ _ U.prop ht), MorphismProperty.Under.homMk t rfl, ?_⟩
  apply CostructuredArrow.hom_ext
  exact h

end toCostructuredArrow

/-- Target denominators are final in the localization costructured-arrow category. -/
@[stacks 05T5 "target denominators are final in the localization comma category"]
instance toCostructuredArrow_final (S : MorphismProperty C)
    [S.HasLeftCalculusOfFractions] (X : C) :
    Functor.Final (toCostructuredArrow S X) := by
  letI := denominators_isFiltered S X
  exact Functor.final_of_exists_of_isFiltered _
    (toCostructuredArrow.exists_hom S)
    (fun {_ U} f g ↦ toCostructuredArrow.exists_equalizer S U f g)

/-- The localization costructured-arrow category is filtered when target denominators admit a
left calculus of fractions. -/
instance costructuredArrow_isFiltered (S : MorphismProperty C)
    [S.HasLeftCalculusOfFractions] (X : C) :
    IsFiltered (CostructuredArrow S.Q (S.Q.obj X)) := by
  letI := denominators_isFiltered S X
  exact IsFiltered.of_final (toCostructuredArrow S X)

/-- A diagram on the localization costructured-arrow category has a colimit exactly when its
restriction to target denominators does. -/
theorem hasColimit_comp_iff (S : MorphismProperty C) [S.HasLeftCalculusOfFractions]
    (X : C) (F : CostructuredArrow S.Q (S.Q.obj X) ⥤ D) :
    HasColimit (toCostructuredArrow S X ⋙ F) ↔ HasColimit F :=
  Functor.Final.hasColimit_comp_iff (toCostructuredArrow S X)

end Under

namespace Over

private theorem denominators_isCofiltered (S : MorphismProperty C)
    [S.HasRightCalculusOfFractions] (X : C) :
    IsCofiltered (MorphismProperty.Over S ⊤ X) where
  nonempty := ⟨MorphismProperty.Over.mk ⊤ (𝟙 X) (S.id_mem X)⟩
  cone_objs U V := by
    obtain ⟨φ, hφ⟩ :=
      (LeftFraction.mk U.hom V.hom V.prop).exists_rightFraction
    exact ⟨MorphismProperty.Over.mk ⊤ (φ.s ≫ U.hom)
      (S.comp_mem _ _ φ.hs U.prop),
      MorphismProperty.Over.homMk φ.s rfl,
      MorphismProperty.Over.homMk φ.f hφ.symm, trivial⟩
  cone_maps {U V} f g := by
    obtain ⟨Z, t, ht, h⟩ := HasRightCalculusOfFractions.ext f.left g.left
      V.hom V.prop ((MorphismProperty.Over.w f).trans (MorphismProperty.Over.w g).symm)
    exact ⟨MorphismProperty.Over.mk ⊤ (t ≫ U.hom)
      (S.comp_mem _ _ ht U.prop), MorphismProperty.Over.homMk t rfl,
      MorphismProperty.Over.Hom.ext h⟩

namespace toStructuredArrow

/-- Every localization structured arrow receives a morphism from a source-denominator stage. -/
theorem exists_hom (S : MorphismProperty C) [S.HasRightCalculusOfFractions]
    {X : C} (Y : StructuredArrow (S.Q.obj X) S.Q) :
    ∃ U : MorphismProperty.Over S ⊤ X,
      Nonempty ((MorphismProperty.Over.toStructuredArrow S X).obj U ⟶ Y) := by
  obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction S.Q S Y.hom
  refine ⟨MorphismProperty.Over.mk ⊤ φ.s φ.hs,
    ⟨StructuredArrow.homMk φ.f ?_⟩⟩
  change (Localization.isoOfHom S.Q S φ.s φ.hs).inv ≫ S.Q.map φ.f = Y.hom
  exact hφ.symm

/-- Parallel comparisons from one source-denominator stage to a localization structured arrow
become equal after a further denominator refinement. -/
theorem exists_equalizer (S : MorphismProperty C) [S.HasRightCalculusOfFractions]
    {X : C} {Y : StructuredArrow (S.Q.obj X) S.Q}
    (U : MorphismProperty.Over S ⊤ X)
    (f g : (MorphismProperty.Over.toStructuredArrow S X).obj U ⟶ Y) :
    ∃ (V : MorphismProperty.Over S ⊤ X) (h : V ⟶ U),
      (MorphismProperty.Over.toStructuredArrow S X).map h ≫ f =
        (MorphismProperty.Over.toStructuredArrow S X).map h ≫ g := by
  have hfg : S.Q.map f.right = S.Q.map g.right := by
    apply (cancel_epi (Localization.isoOfHom S.Q S U.hom U.prop).inv).1
    exact (StructuredArrow.w f).trans (StructuredArrow.w g).symm
  obtain ⟨Z, t, ht, h⟩ := (map_eq_iff_precomp S.Q S f.right g.right).1 hfg
  refine ⟨MorphismProperty.Over.mk ⊤ (t ≫ U.hom)
    (S.comp_mem _ _ ht U.prop), MorphismProperty.Over.homMk t rfl, ?_⟩
  apply StructuredArrow.hom_ext
  exact h

end toStructuredArrow

/-- Source denominators are initial in the localization structured-arrow category. -/
@[stacks 05T5 "source denominators are initial in the localization comma category"]
instance toStructuredArrow_initial (S : MorphismProperty C)
    [S.HasRightCalculusOfFractions] (X : C) :
    Functor.Initial (toStructuredArrow S X) := by
  letI := denominators_isCofiltered S X
  exact Functor.initial_of_exists_of_isCofiltered _
    (toStructuredArrow.exists_hom S)
    (fun {_ U} f g ↦ toStructuredArrow.exists_equalizer S U f g)

/-- The localization structured-arrow category is cofiltered when source denominators admit a
right calculus of fractions. -/
instance structuredArrow_isCofiltered (S : MorphismProperty C)
    [S.HasRightCalculusOfFractions] (X : C) :
    IsCofiltered (StructuredArrow (S.Q.obj X) S.Q) := by
  letI := denominators_isCofiltered S X
  exact IsCofiltered.of_initial (toStructuredArrow S X)

/-- A diagram on the localization structured-arrow category has a limit exactly when its
restriction to source denominators does. -/
theorem hasLimit_comp_iff (S : MorphismProperty C) [S.HasRightCalculusOfFractions]
    (X : C) (F : StructuredArrow (S.Q.obj X) S.Q ⥤ D) :
    HasLimit (toStructuredArrow S X ⋙ F) ↔ HasLimit F :=
  Functor.Initial.hasLimit_comp_iff (toStructuredArrow S X)

end Over



end CategoryTheory.MorphismProperty
