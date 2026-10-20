module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.AssocLeftProjection.Basic

/-!
# Computations for left-projection reassociation

Object, morphism, and projection-comparison formulas for the explicit reassociation functors.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoricalPullback

namespace CategoryTheory

universe vA' vA vB vD
universe uA' uA uB uD

namespace Limits.CategoricalPullback.LeftProjection

variable {A₀' : Type uA'} [Category.{vA'} A₀']
variable {A₀ : Type uA} [Category.{vA} A₀]
variable {B₀ : Type uB} [Category.{vB} B₀]
variable {D₀ : Type uD} [Category.{vD} D₀]

variable (K : A₀' ⥤ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)

namespace forward

/-- Forward reassociation retains the outer left object. -/
@[simp]
theorem obj.fst (x : K ⊡ (π₁ F G)) :
    ((LeftProjection.forward K F G).obj x).fst = x.fst := sorry

/-- Forward reassociation retains the inner right object. -/
@[simp]
theorem obj.snd (x : K ⊡ (π₁ F G)) :
    ((LeftProjection.forward K F G).obj x).snd = x.snd.snd := sorry

/-- The forward structural isomorphism is the composite of the outer comparison transported by
`F` and the inner comparison. -/
@[simp]
theorem obj.iso (x : K ⊡ (π₁ F G)) :
    ((LeftProjection.forward K F G).obj x).iso = F.mapIso x.iso ≪≫ x.snd.iso := sorry

/-- On morphisms, forward reassociation retains the outer left component. -/
@[simp]
theorem hom.fst {x y : K ⊡ (π₁ F G)} (φ : x ⟶ y) :
    ((LeftProjection.forward K F G).map φ).fst = φ.fst := sorry

/-- On morphisms, forward reassociation retains the inner right component. -/
@[simp]
theorem hom.snd {x y : K ⊡ (π₁ F G)} (φ : x ⟶ y) :
    ((LeftProjection.forward K F G).map φ).snd = φ.snd.snd := sorry

/-- The forward component of the left-projection comparison is the identity. -/
@[simp]
theorem fstIso.hom.app (x : K ⊡ (π₁ F G)) :
    (LeftProjection.forward.fstIso K F G).hom.app x = 𝟙 _ := sorry

/-- The inverse component of the left-projection comparison is the identity. -/
@[simp]
theorem fstIso.inv.app (x : K ⊡ (π₁ F G)) :
    (LeftProjection.forward.fstIso K F G).inv.app x = 𝟙 _ := sorry

/-- The forward component of the right-projection comparison is the identity. -/
@[simp]
theorem sndIso.hom.app (x : K ⊡ (π₁ F G)) :
    (LeftProjection.forward.sndIso K F G).hom.app x = 𝟙 _ := sorry

/-- The inverse component of the right-projection comparison is the identity. -/
@[simp]
theorem sndIso.inv.app (x : K ⊡ (π₁ F G)) :
    (LeftProjection.forward.sndIso K F G).inv.app x = 𝟙 _ := sorry

end forward

namespace inverse

/-- Inverse reassociation retains the leftmost object. -/
@[simp]
theorem obj.fst (x : (K ⋙ F) ⊡ G) :
    ((LeftProjection.inverse K F G).obj x).fst = x.fst := sorry

/-- The inner left object inserted by inverse reassociation is `K.obj x.fst`. -/
@[simp]
theorem obj.sndFst (x : (K ⋙ F) ⊡ G) :
    ((LeftProjection.inverse K F G).obj x).snd.fst = K.obj x.fst := sorry

/-- Inverse reassociation retains the right object of the target pullback. -/
@[simp]
theorem obj.sndSnd (x : (K ⋙ F) ⊡ G) :
    ((LeftProjection.inverse K F G).obj x).snd.snd = x.snd := sorry

/-- The inner structural isomorphism inserted by inverse reassociation is `x.iso`. -/
@[simp]
theorem obj.sndIso (x : (K ⋙ F) ⊡ G) :
    ((LeftProjection.inverse K F G).obj x).snd.iso = x.iso := sorry

/-- The outer structural isomorphism inserted by inverse reassociation is the identity. -/
@[simp]
theorem obj.iso (x : (K ⋙ F) ⊡ G) :
    ((LeftProjection.inverse K F G).obj x).iso = Iso.refl (K.obj x.fst) := sorry

/-- On morphisms, inverse reassociation retains the left component. -/
@[simp]
theorem hom.fst {x y : (K ⋙ F) ⊡ G} (φ : x ⟶ y) :
    ((LeftProjection.inverse K F G).map φ).fst = φ.fst := sorry

/-- On morphisms, inverse reassociation applies `K` to the inserted inner left component. -/
@[simp]
theorem hom.sndFst {x y : (K ⋙ F) ⊡ G} (φ : x ⟶ y) :
    ((LeftProjection.inverse K F G).map φ).snd.fst = K.map φ.fst := sorry

/-- On morphisms, inverse reassociation retains the target pullback's right component. -/
@[simp]
theorem hom.sndSnd {x y : (K ⋙ F) ⊡ G} (φ : x ⟶ y) :
    ((LeftProjection.inverse K F G).map φ).snd.snd = φ.snd := sorry

/-- The forward component of the inverse left-projection comparison is the identity. -/
@[simp]
theorem fstIso.hom.app (x : (K ⋙ F) ⊡ G) :
    (LeftProjection.inverse.fstIso K F G).hom.app x = 𝟙 _ := sorry

/-- The inverse component of the inverse left-projection comparison is the identity. -/
@[simp]
theorem fstIso.inv.app (x : (K ⋙ F) ⊡ G) :
    (LeftProjection.inverse.fstIso K F G).inv.app x = 𝟙 _ := sorry

/-- The forward component of the inverse right-projection comparison is the identity. -/
@[simp]
theorem sndIso.hom.app (x : (K ⋙ F) ⊡ G) :
    (LeftProjection.inverse.sndIso K F G).hom.app x = 𝟙 _ := sorry

/-- The inverse component of the inverse right-projection comparison is the identity. -/
@[simp]
theorem sndIso.inv.app (x : (K ⋙ F) ⊡ G) :
    (LeftProjection.inverse.sndIso K F G).inv.app x = 𝟙 _ := sorry

end inverse

end Limits.CategoricalPullback.LeftProjection

end CategoryTheory
