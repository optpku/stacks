/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Pseudofunctor
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

/-!
# Strong transformations from an existing full-subbicategory pseudofunctor

This construction lifts only the ambient target of a strong transformation. The source remains
the supplied pseudofunctor into the full subbicategory, preserving its canonical owner and exact
endpoint.
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

namespace Implementation.LiftFrom

variable (G : Pseudofunctor A P.FullSubbicategory) (H : Pseudofunctor A D)
variable (hH : ∀ X : A, P (H.obj X))
variable (η : Pseudofunctor.StrongTrans
  (G.comp (FullSubbicategory.ι P).toPseudofunctor) H)

/-- An ambient component from the forgotten bundled source, regarded in the full
subbicategory. -/
private def app (X : A) :
    G.obj X ⟶ (FullSubbicategory.liftPseudofunctor H hH).obj X :=
  Bicategory.InducedBicategory.mkHom (η.app X)

/-- An ambient naturality isomorphism from the forgotten bundled source, regarded in the full
subbicategory. -/
private def naturality {X Y : A} (f : X ⟶ Y) :
    G.map f ≫ app G H hH η Y ≅
      app G H hH η X ≫
        (FullSubbicategory.liftPseudofunctor H hH).map f :=
  Bicategory.InducedBicategory.isoMk (η.naturality f)

/-- Naturality in source `2`-morphisms after lifting only the target endpoint. -/
private theorem naturality₂ :
    ∀ {X Y : A} {f g : X ⟶ Y} (θ : f ⟶ g),
      G.map₂ θ ▷ app G H hH η Y ≫
          (naturality G H hH η g).hom =
        (naturality G H hH η f).hom ≫
          app G H hH η X ◁
            (FullSubbicategory.liftPseudofunctor H hH).map₂ θ := sorry

/-- Identity coherence after lifting only the target endpoint. -/
private theorem naturalityId :
    ∀ X : A,
      (naturality G H hH η (𝟙 X)).hom ≫
          app G H hH η X ◁
            ((FullSubbicategory.liftPseudofunctor H hH).mapId X).hom =
        (G.mapId X).hom ▷ app G H hH η X ≫
          (λ_ (app G H hH η X)).hom ≫
          (ρ_ (app G H hH η X)).inv := sorry

/-- Composition coherence after lifting only the target endpoint. -/
private theorem naturalityComp :
    ∀ {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z),
      (naturality G H hH η (f ≫ g)).hom ≫
          app G H hH η X ◁
            ((FullSubbicategory.liftPseudofunctor H hH).mapComp f g).hom =
        (G.mapComp f g).hom ▷ app G H hH η Z ≫
          (α_ _ _ _).hom ≫
          G.map f ◁ (naturality G H hH η g).hom ≫
          (α_ _ _ _).inv ≫
          (naturality G H hH η f).hom ▷
            (FullSubbicategory.liftPseudofunctor H hH).map g ≫
          (α_ _ _ _).hom := sorry

end Implementation.LiftFrom

/-- Lift an ambient strong transformation directly from an existing pseudofunctor into the full
subbicategory. Only the target pseudofunctor is repackaged. -/
def liftFrom (G : Pseudofunctor A P.FullSubbicategory) (H : Pseudofunctor A D)
    (hH : ∀ X : A, P (H.obj X))
    (η : Pseudofunctor.StrongTrans
      (G.comp (FullSubbicategory.ι P).toPseudofunctor) H) :
    Pseudofunctor.StrongTrans G
      (FullSubbicategory.liftPseudofunctor H hH) where
  app := Implementation.LiftFrom.app G H hH η
  naturality := Implementation.LiftFrom.naturality G H hH η
  naturality_naturality := Implementation.LiftFrom.naturality₂ G H hH η
  naturality_id := Implementation.LiftFrom.naturalityId G H hH η
  naturality_comp := Implementation.LiftFrom.naturalityComp G H hH η

end ObjectProperty.FullSubbicategory.StrongTrans

end CategoryTheory
