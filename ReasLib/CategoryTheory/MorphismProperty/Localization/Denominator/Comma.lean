/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.CategoryTheory.MorphismProperty.Comma

/-!
# Denominator categories and localization comma categories

Target denominators under an object map canonically to the costructured-arrow category which
indexes pointwise left Kan extensions along a localization.  Dually, source denominators over an
object map to the corresponding structured-arrow category.

The functors in this file are explicit data.  Their coherence is isolated in the two
`localizationInv_naturality` lemmas, so deferred proof obligations do not hide any object or map.
-/

@[expose] public section

universe v u

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C]

namespace Under

/-- Inverting target denominators in a localization is natural along denominator refinements. -/
@[reassoc]
theorem localizationInv_naturality (S : MorphismProperty C) {X : C}
    {U V : MorphismProperty.Under S ⊤ X} (f : U ⟶ V) :
    S.Q.map f.right ≫ (Localization.isoOfHom S.Q S V.hom V.prop).inv =
      (Localization.isoOfHom S.Q S U.hom U.prop).inv := sorry

/-- Target denominators under `X` form a canonical family of costructured arrows over the
localization of `X`. -/
@[stacks 05T5 "target-denominator localization comma functor"]
noncomputable def toCostructuredArrow (S : MorphismProperty C) (X : C) :
    MorphismProperty.Under S ⊤ X ⥤ CostructuredArrow S.Q (S.Q.obj X) :=
  (MorphismProperty.Under.forget S ⊤ X ⋙ CategoryTheory.Under.forget X).toCostructuredArrow
    S.Q (S.Q.obj X) (fun U ↦ (Localization.isoOfHom S.Q S U.hom U.prop).inv)
    (fun f ↦ localizationInv_naturality S f)

/-- The object of the localization comma category associated to a target denominator has the
localized denominator target as its source. -/
@[simp]
theorem toCostructuredArrow_obj_left (S : MorphismProperty C) (X : C)
    (U : MorphismProperty.Under S ⊤ X) :
    ((toCostructuredArrow S X).obj U).left = U.right := sorry

/-- The structural morphism associated to a target denominator is its inverse after
localization. -/
@[simp]
theorem toCostructuredArrow_obj_hom (S : MorphismProperty C) (X : C)
    (U : MorphismProperty.Under S ⊤ X) :
    ((toCostructuredArrow S X).obj U).hom =
      (Localization.isoOfHom S.Q S U.hom U.prop).inv := sorry

/-- A target-denominator refinement is sent to the localization of its target map. -/
@[simp]
theorem toCostructuredArrow_map_left (S : MorphismProperty C) (X : C)
    {U V : MorphismProperty.Under S ⊤ X} (f : U ⟶ V) :
    ((toCostructuredArrow S X).map f).left = f.right := sorry

/-- Forgetting a target denominator's costructured-arrow structure recovers its localized target
functor. -/
@[simp]
theorem toCostructuredArrow_comp_proj (S : MorphismProperty C) (X : C) :
    toCostructuredArrow S X ⋙ CostructuredArrow.proj S.Q (S.Q.obj X) =
      MorphismProperty.Under.forget S ⊤ X ⋙ CategoryTheory.Under.forget X := sorry

end Under

namespace Over

/-- Inverting source denominators in a localization is natural along denominator refinements. -/
@[reassoc]
theorem localizationInv_naturality (S : MorphismProperty C) {X : C}
    {U V : MorphismProperty.Over S ⊤ X} (f : U ⟶ V) :
    (Localization.isoOfHom S.Q S U.hom U.prop).inv ≫ S.Q.map f.left =
      (Localization.isoOfHom S.Q S V.hom V.prop).inv := sorry

/-- Source denominators over `X` form a canonical family of structured arrows under the
localization of `X`. -/
@[stacks 05T5 "source-denominator localization comma functor"]
noncomputable def toStructuredArrow (S : MorphismProperty C) (X : C) :
    MorphismProperty.Over S ⊤ X ⥤ StructuredArrow (S.Q.obj X) S.Q :=
  (MorphismProperty.Over.forget S ⊤ X ⋙ CategoryTheory.Over.forget X).toStructuredArrow
    (S.Q.obj X) S.Q (fun U ↦ (Localization.isoOfHom S.Q S U.hom U.prop).inv)
    (fun f ↦ localizationInv_naturality S f)

/-- The object of the localization comma category associated to a source denominator has the
localized denominator source as its target. -/
@[simp]
theorem toStructuredArrow_obj_right (S : MorphismProperty C) (X : C)
    (U : MorphismProperty.Over S ⊤ X) :
    ((toStructuredArrow S X).obj U).right = U.left := sorry

/-- The structural morphism associated to a source denominator is its inverse after
localization. -/
@[simp]
theorem toStructuredArrow_obj_hom (S : MorphismProperty C) (X : C)
    (U : MorphismProperty.Over S ⊤ X) :
    ((toStructuredArrow S X).obj U).hom =
      (Localization.isoOfHom S.Q S U.hom U.prop).inv := sorry

/-- A source-denominator refinement is sent to the localization of its source map. -/
@[simp]
theorem toStructuredArrow_map_right (S : MorphismProperty C) (X : C)
    {U V : MorphismProperty.Over S ⊤ X} (f : U ⟶ V) :
    ((toStructuredArrow S X).map f).right = f.left := sorry

/-- Forgetting a source denominator's structured-arrow structure recovers its localized source
functor. -/
@[simp]
theorem toStructuredArrow_comp_proj (S : MorphismProperty C) (X : C) :
    toStructuredArrow S X ⋙ StructuredArrow.proj (S.Q.obj X) S.Q =
      MorphismProperty.Over.forget S ⊤ X ⋙ CategoryTheory.Over.forget X := sorry

end Over




end CategoryTheory.MorphismProperty
