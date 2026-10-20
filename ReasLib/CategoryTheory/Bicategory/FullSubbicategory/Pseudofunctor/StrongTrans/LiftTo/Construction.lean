/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Pseudofunctor
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

/-!
# Strong transformations to an existing full-subbicategory pseudofunctor

This construction lifts only the ambient source of a strong transformation. The target remains
the supplied pseudofunctor into the full subbicategory, so canonical target owners such as cospan
projections are retained without endpoint wrappers or equality transport.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

universe w v u wA vA uA

namespace ObjectProperty.FullSubbicategory.StrongTrans

variable {D : Type u} [Bicategory.{w, v} D]
variable {P : ObjectProperty D}
variable {A : Type uA} [Bicategory.{wA, vA} A]

namespace Implementation.LiftTo

variable (G : Pseudofunctor A D) (H : Pseudofunctor A P.FullSubbicategory)
variable (hG : ∀ X : A, P (G.obj X))
variable (η : Pseudofunctor.StrongTrans G
  (H.comp (FullSubbicategory.ι P).toPseudofunctor))

/-- An ambient component into the forgotten bundled target, regarded in the full
subbicategory. -/
private def app (X : A) :
    (FullSubbicategory.liftPseudofunctor G hG).obj X ⟶ H.obj X :=
  Bicategory.InducedBicategory.mkHom (η.app X)

/-- An ambient naturality isomorphism into the forgotten bundled target, regarded in the full
subbicategory. -/
private def naturality {X Y : A} (f : X ⟶ Y) :
    (FullSubbicategory.liftPseudofunctor G hG).map f ≫ app G H hG η Y ≅
      app G H hG η X ≫ H.map f :=
  Bicategory.InducedBicategory.isoMk (η.naturality f)

/-- Naturality in source `2`-morphisms after lifting only the source endpoint. -/
private theorem naturality₂ :
    ∀ {X Y : A} {f g : X ⟶ Y} (θ : f ⟶ g),
      (FullSubbicategory.liftPseudofunctor G hG).map₂ θ ▷ app G H hG η Y ≫
          (naturality G H hG η g).hom =
        (naturality G H hG η f).hom ≫
          app G H hG η X ◁ H.map₂ θ := sorry

/-- Identity coherence after lifting only the source endpoint. -/
private theorem naturalityId :
    ∀ X : A,
      (naturality G H hG η (𝟙 X)).hom ≫
          app G H hG η X ◁ (H.mapId X).hom =
        ((FullSubbicategory.liftPseudofunctor G hG).mapId X).hom ▷
            app G H hG η X ≫
          (λ_ (app G H hG η X)).hom ≫
          (ρ_ (app G H hG η X)).inv := sorry

/-- Composition coherence after lifting only the source endpoint. -/
private theorem naturalityComp :
    ∀ {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z),
      (naturality G H hG η (f ≫ g)).hom ≫
          app G H hG η X ◁ (H.mapComp f g).hom =
        ((FullSubbicategory.liftPseudofunctor G hG).mapComp f g).hom ▷
            app G H hG η Z ≫
          (α_ _ _ _).hom ≫
          (FullSubbicategory.liftPseudofunctor G hG).map f ◁
            (naturality G H hG η g).hom ≫
          (α_ _ _ _).inv ≫
          (naturality G H hG η f).hom ▷ H.map g ≫
          (α_ _ _ _).hom := sorry

end Implementation.LiftTo

/-- Lift an ambient strong transformation directly to an existing pseudofunctor into the full
subbicategory. Only the source pseudofunctor is repackaged. -/
def liftTo (G : Pseudofunctor A D) (H : Pseudofunctor A P.FullSubbicategory)
    (hG : ∀ X : A, P (G.obj X))
    (η : Pseudofunctor.StrongTrans G
      (H.comp (FullSubbicategory.ι P).toPseudofunctor)) :
    Pseudofunctor.StrongTrans
      (FullSubbicategory.liftPseudofunctor G hG) H where
  app := Implementation.LiftTo.app G H hG η
  naturality := Implementation.LiftTo.naturality G H hG η
  naturality_naturality := Implementation.LiftTo.naturality₂ G H hG η
  naturality_id := Implementation.LiftTo.naturalityId G H hG η
  naturality_comp := Implementation.LiftTo.naturalityComp G H hG η

end ObjectProperty.FullSubbicategory.StrongTrans

end CategoryTheory
