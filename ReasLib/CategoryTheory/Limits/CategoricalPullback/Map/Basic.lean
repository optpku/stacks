module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver

/-!
# Maps of categorical pullbacks

Cospan transformations induce functors between explicit categorical pullbacks. This module owns
the induced functor and its object- and morphism-level computation interface.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoricalPullback
open scoped CategoricalPullback

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉

variable {X : Type u₁} [Category.{v₁} X]
variable {Y : Type u₂} [Category.{v₂} Y]
variable {Z : Type u₃} [Category.{v₃} Z]
variable {A : Type u₄} [Category.{v₄} A]
variable {B : Type u₅} [Category.{v₅} B]
variable {C : Type u₆} [Category.{v₆} C]

namespace Limits.CategoricalPullback

variable {H : X ⥤ Z} {I : Y ⥤ Z} {F : A ⥤ C} {G : B ⥤ C}

/-- For fixed source and target cospans, cospan transformations act functorially on their
categorical pullbacks. Morphisms between transformations become natural transformations between
the induced functors. -/
def mapFunctor : CatCospanTransform H I F G ⥤ (H ⊡ I ⥤ F ⊡ G) :=
  (CatCommSqOver.transform (H ⊡ I)).flip.obj (catCommSqOver H I) ⋙
    CatCommSqOver.toFunctorToCategoricalPullback F G (H ⊡ I)

/-- The functor between categorical pullbacks induced by a cospan transformation. -/
def map (ψ : CatCospanTransform H I F G) : H ⊡ I ⥤ F ⊡ G :=
  mapFunctor.obj ψ

/-- The left object component of the pullback map induced by a cospan transformation. -/
@[simp]
theorem map.obj.fst (ψ : CatCospanTransform H I F G) (P : H ⊡ I) :
    (map ψ |>.obj P).fst = ψ.left.obj P.fst := sorry

/-- The right object component of the pullback map induced by a cospan transformation. -/
@[simp]
theorem map.obj.snd (ψ : CatCospanTransform H I F G) (P : H ⊡ I) :
    (map ψ |>.obj P).snd = ψ.right.obj P.snd := sorry

/-- The structural isomorphism of the image of a pullback object under a cospan
transformation. -/
@[simp]
theorem map.obj.iso (ψ : CatCospanTransform H I F G) (P : H ⊡ I) :
    (map ψ |>.obj P).iso =
      ψ.squareLeft.iso.symm.app P.fst ≪≫
        ψ.base.mapIso P.iso ≪≫
        ψ.squareRight.iso.app P.snd := sorry

/-- Forward-map computation for the structural isomorphism of a pullback object transported by
a cospan transformation. -/
@[simp]
theorem map.obj.iso.hom (ψ : CatCospanTransform H I F G) (P : H ⊡ I) :
    (map ψ |>.obj P).iso.hom =
      ψ.squareLeft.iso.inv.app P.fst ≫
        ψ.base.map P.iso.hom ≫
        ψ.squareRight.iso.hom.app P.snd := sorry

/-- Inverse-map computation for the structural isomorphism of a pullback object transported by
a cospan transformation. -/
@[simp]
theorem map.obj.iso.inv (ψ : CatCospanTransform H I F G) (P : H ⊡ I) :
    (map ψ |>.obj P).iso.inv =
      ψ.squareRight.iso.inv.app P.snd ≫
        ψ.base.map P.iso.inv ≫
        ψ.squareLeft.iso.hom.app P.fst := sorry

/-- The left morphism component of the pullback map induced by a cospan transformation. -/
@[simp]
theorem map.hom.fst (ψ : CatCospanTransform H I F G)
    {P Q : H ⊡ I} (φ : P ⟶ Q) :
    (map ψ |>.map φ).fst = ψ.left.map φ.fst := sorry

/-- The right morphism component of the pullback map induced by a cospan transformation. -/
@[simp]
theorem map.hom.snd (ψ : CatCospanTransform H I F G)
    {P Q : H ⊡ I} (φ : P ⟶ Q) :
    (map ψ |>.map φ).snd = ψ.right.map φ.snd := sorry

end Limits.CategoricalPullback

end CategoryTheory

/- Axiom audit: the functor and its induced map are explicit data owners. -/
