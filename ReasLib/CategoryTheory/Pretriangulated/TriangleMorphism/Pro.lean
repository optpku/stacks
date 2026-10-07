module

public import ReasLib.CategoryTheory.Pro.Representative
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Pro-values represented by morphisms of triangles

A morphism from one stage of a triangle-valued diagram to a fixed triangle is a pro-value map
when each of its three vertex morphisms represents the corresponding Hom-colimit.
-/

@[expose] public section

open CategoryTheory Limits Opposite
open scoped CategoryTheory

universe uD vD uI vI

namespace CategoryTheory.Pretriangulated.TriangleMorphism

variable {D : Type uD} [Category.{vD} D] [HasShift D ℤ]
variable {I : Type uI} [Category.{vI} I] [Small.{vD} I]

/-- A morphism from a stage of a triangle-valued diagram to a fixed triangle represents the
Hom-colimits of its first, second, and third vertex diagrams. This is the triangle-map vocabulary
used by Lemma 13.42.2 (0G3A). -/
@[stacks 0G3A]
structure IsHomColimitRepresentative {T : I ⥤ Triangle D} {U : Triangle D} {i : I}
    (φ : T.obj i ⟶ U) : Prop where
  /-- The first vertex map represents its Hom-colimit. -/
  first :
    (CostructuredArrow.mk φ.hom₁ : CostructuredArrow (T ⋙ Triangle.π₁) U.obj₁).IsHomColimitRepresentative
  /-- The second vertex map represents its Hom-colimit. -/
  second :
    (CostructuredArrow.mk φ.hom₂ : CostructuredArrow (T ⋙ Triangle.π₂) U.obj₂).IsHomColimitRepresentative
  /-- The third vertex map represents its Hom-colimit. -/
  third :
    (CostructuredArrow.mk φ.hom₃ : CostructuredArrow (T ⋙ Triangle.π₃) U.obj₃).IsHomColimitRepresentative

/-- The first component of a representing triangle morphism supplies the first pro-value. -/
theorem hasValue_first {T : I ⥤ Triangle D} {U : Triangle D} {i : I}
    {φ : T.obj i ⟶ U} (h : IsHomColimitRepresentative φ) :
    Pro.HasValue (T ⋙ Triangle.π₁) U.obj₁ := sorry

/-- The second component of a representing triangle morphism supplies the second pro-value. -/
theorem hasValue_second {T : I ⥤ Triangle D} {U : Triangle D} {i : I}
    {φ : T.obj i ⟶ U} (h : IsHomColimitRepresentative φ) :
    Pro.HasValue (T ⋙ Triangle.π₂) U.obj₂ := sorry

/-- The third component of a representing triangle morphism supplies the third pro-value. -/
theorem hasValue_third {T : I ⥤ Triangle D} {U : Triangle D} {i : I}
    {φ : T.obj i ⟶ U} (h : IsHomColimitRepresentative φ) :
    Pro.HasValue (T ⋙ Triangle.π₃) U.obj₃ := sorry

end CategoryTheory.Pretriangulated.TriangleMorphism
