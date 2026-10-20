module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.OuterProjection.Basic

/-!
# Computations for the outer projection of an iterated categorical pullback

This leaf exposes the cospan-transformation, projection-isomorphism, object, and morphism formulas
of `OuterProjection.ofIso`.
-/

@[expose] public section

open CategoryTheory.Limits
open scoped CategoricalPullback

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]
variable {D : Type u₄} [Category.{v₄} D]
variable {E : Type u₅} [Category.{v₅} E]
variable {F : Type u₆} [Category.{v₆} F]

namespace Limits.CategoricalPullback

variable (AB : A ⥤ B) (ED : E ⥤ D)
variable {CB : C ⥤ B} {CD : C ⥤ D} {BF : B ⥤ F} {DF : D ⥤ F}

namespace OuterProjection

namespace transform

/-- The left leg of the outer-projection cospan transformation is the inner first
projection. -/
@[simp] theorem left (comm : CB ⋙ BF ≅ CD ⋙ DF) :
    (transform AB ED comm).left = π₁ AB CB := sorry

/-- The base leg of the outer-projection cospan transformation is `DF`. -/
@[simp] theorem base (comm : CB ⋙ BF ≅ CD ⋙ DF) :
    (transform AB ED comm).base = DF := sorry

/-- The right leg of the outer-projection cospan transformation is the identity of `E`. -/
@[simp] theorem right (comm : CB ⋙ BF ≅ CD ⋙ DF) :
    (transform AB ED comm).right = 𝟭 E := sorry

/-- The left comparison cell of the outer-projection cospan transformation is
`transform.leftIso`. -/
@[simp] theorem squareLeft.iso (comm : CB ⋙ BF ≅ CD ⋙ DF) :
    (transform AB ED comm).squareLeft.iso = leftIso AB comm := sorry

/-- The right comparison cell of the outer-projection cospan transformation is the inverse
left unitor of `ED ⋙ DF`. -/
@[simp] theorem squareRight.iso (comm : CB ⋙ BF ≅ CD ⋙ DF) :
    (transform AB ED comm).squareRight.iso =
      (Functor.leftUnitor (ED ⋙ DF)).symm := sorry

end transform

namespace ofIso

/-- The forward component of the first-projection comparison for the generalized outer
projection is the identity. -/
@[simp] theorem fstIso.hom.app (comm : CB ⋙ BF ≅ CD ⋙ DF)
    (x : ((π₂ AB CB) ⋙ CD) ⊡ ED) :
    (fstIso AB ED comm).hom.app x = 𝟙 _ := sorry

/-- The inverse component of the first-projection comparison for the generalized outer
projection is the identity. -/
@[simp] theorem fstIso.inv.app (comm : CB ⋙ BF ≅ CD ⋙ DF)
    (x : ((π₂ AB CB) ⋙ CD) ⊡ ED) :
    (fstIso AB ED comm).inv.app x = 𝟙 _ := sorry

/-- The forward component of the second-projection comparison for the generalized outer
projection is the right-unitor component of the source's second projection. -/
@[simp] theorem sndIso.hom.app (comm : CB ⋙ BF ≅ CD ⋙ DF)
    (x : ((π₂ AB CB) ⋙ CD) ⊡ ED) :
    (sndIso AB ED comm).hom.app x =
      (Functor.rightUnitor (π₂ ((π₂ AB CB) ⋙ CD) ED)).hom.app x := sorry

/-- The inverse component of the second-projection comparison for the generalized outer
projection is the inverse right-unitor component of the source's second projection. -/
@[simp] theorem sndIso.inv.app (comm : CB ⋙ BF ≅ CD ⋙ DF)
    (x : ((π₂ AB CB) ⋙ CD) ⊡ ED) :
    (sndIso AB ED comm).inv.app x =
      (Functor.rightUnitor (π₂ ((π₂ AB CB) ⋙ CD) ED)).inv.app x := sorry

/-- The first object selected by the generalized outer projection is the inner pullback's first
object. -/
@[simp] theorem obj.fst (comm : CB ⋙ BF ≅ CD ⋙ DF)
    (x : ((π₂ AB CB) ⋙ CD) ⊡ ED) :
    ((ofIso AB ED comm).obj x).fst = x.fst.fst := sorry

/-- The second object selected by the generalized outer projection is the outer pullback's
second object. -/
@[simp] theorem obj.snd (comm : CB ⋙ BF ≅ CD ⋙ DF)
    (x : ((π₂ AB CB) ⋙ CD) ⊡ ED) :
    ((ofIso AB ED comm).obj x).snd = x.snd := sorry

/-- The structural isomorphism of the generalized outer projection is the composite along the
inner pullback, the comparison cell, and the outer pullback. -/
@[simp] theorem obj.iso (comm : CB ⋙ BF ≅ CD ⋙ DF)
    (x : ((π₂ AB CB) ⋙ CD) ⊡ ED) :
    ((ofIso AB ED comm).obj x).iso =
      BF.mapIso x.fst.iso ≪≫ comm.app x.fst.snd ≪≫ DF.mapIso x.iso := sorry

/-- On morphisms, the generalized outer projection retains the inner first component. -/
@[simp] theorem map.fst (comm : CB ⋙ BF ≅ CD ⋙ DF)
    {x y : ((π₂ AB CB) ⋙ CD) ⊡ ED} (f : x ⟶ y) :
    ((ofIso AB ED comm).map f).fst = f.fst.fst := sorry

/-- On morphisms, the generalized outer projection retains the outer second component. -/
@[simp] theorem map.snd (comm : CB ⋙ BF ≅ CD ⋙ DF)
    {x y : ((π₂ AB CB) ⋙ CD) ⊡ ED} (f : x ⟶ y) :
    ((ofIso AB ED comm).map f).snd = f.snd := sorry

end ofIso

end OuterProjection

end Limits.CategoricalPullback

end CategoryTheory
