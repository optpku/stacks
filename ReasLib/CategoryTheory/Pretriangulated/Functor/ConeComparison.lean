module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparing Triangulated Functors on Cones

A natural isomorphism on a full subcategory compares the images of every one-step cone of a
morphism in that subcategory, provided both functors are triangulated.  The explicit triangle
isomorphism is exposed for downstream arguments that need its three components.
-/

@[expose] public section

noncomputable section

open CategoryTheory.Pretriangulated
open CategoryTheory.Limits

universe vC uC vD uD

namespace CategoryTheory

namespace ObjectProperty

variable {C : Type uC} [Category.{vC} C]
variable [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
variable [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The one-step cone closure of an object property: `P.coneOfMap Z` means that `Z` is the
third object of a distinguished triangle whose first two objects satisfy `P`. -/
@[stacks 09SB "one-step cone closure"]
def coneOfMap (P : ObjectProperty C) : ObjectProperty C :=
  fun Z ↦ ∃ (X Y : C) (_ : P X) (_ : P Y)
      (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧),
    Triangle.mk f g h ∈ distTriang C

/-- Membership in `P.coneOfMap` is the existence of a distinguished cone triangle whose
first two objects satisfy `P`. -/
theorem coneOfMap_iff (P : ObjectProperty C) (Z : C) :
    P.coneOfMap Z ↔
      ∃ (X Y : C) (_ : P X) (_ : P Y)
          (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧),
        Triangle.mk f g h ∈ distTriang C := sorry

end ObjectProperty

namespace Functor.ConeComparison

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable [HasZeroObject C] [HasZeroObject D]
variable [Preadditive C] [Preadditive D]
variable [HasShift C ℤ] [HasShift D ℤ]
variable [∀ n : ℤ, (shiftFunctor C n).Additive]
variable [∀ n : ℤ, (shiftFunctor D n).Additive]
variable [Pretriangulated C] [Pretriangulated D]
variable {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
variable [F.IsTriangulated] [G.IsTriangulated]

/-- Naturality of a comparison on a full subcategory gives the commutative first square needed
to compare the images of a cone triangle. -/
theorem comm₁ (P : ObjectProperty C) (e : P.ι ⋙ F ≅ P.ι ⋙ G)
    (T : Triangle C) (h₁ : P T.obj₁) (h₂ : P T.obj₂) :
    F.map T.mor₁ ≫ (e.app ⟨T.obj₂, h₂⟩).hom =
      (e.app ⟨T.obj₁, h₁⟩).hom ≫ G.map T.mor₁ := sorry

/-- The canonical comparison of the images of a distinguished triangle, constructed from a
natural isomorphism on a full subcategory containing its first two objects. -/
def triangleIso (P : ObjectProperty C) (e : P.ι ⋙ F ≅ P.ι ⋙ G)
    (T : Triangle C) (hT : T ∈ distTriang C) (h₁ : P T.obj₁) (h₂ : P T.obj₂) :
    F.mapTriangle.obj T ≅ G.mapTriangle.obj T :=
  Pretriangulated.isoTriangleOfIso₁₂ (F.mapTriangle.obj T) (G.mapTriangle.obj T)
    (F.map_distinguished T hT) (G.map_distinguished T hT)
    (e.app ⟨T.obj₁, h₁⟩) (e.app ⟨T.obj₂, h₂⟩) (comm₁ P e T h₁ h₂)

/-- The third component of `triangleIso`, comparing the two functors on the cone object. -/
def coneIso (P : ObjectProperty C) (e : P.ι ⋙ F ≅ P.ι ⋙ G)
    (T : Triangle C) (hT : T ∈ distTriang C) (h₁ : P T.obj₁) (h₂ : P T.obj₂) :
    F.obj T.obj₃ ≅ G.obj T.obj₃ :=
  Triangle.π₃.mapIso (triangleIso P e T hT h₁ h₂)

/-- If two triangulated functors are naturally isomorphic on a full subcategory, their values
are isomorphic on every one-step cone of a map in that subcategory. -/
@[stacks 09SB "comparison of triangulated functors on cones"]
theorem nonempty_objIso (P : ObjectProperty C) (e : P.ι ⋙ F ≅ P.ι ⋙ G)
    {Z : C} (hZ : P.coneOfMap Z) : Nonempty (F.obj Z ≅ G.obj Z) := sorry

end Functor.ConeComparison

end CategoryTheory
