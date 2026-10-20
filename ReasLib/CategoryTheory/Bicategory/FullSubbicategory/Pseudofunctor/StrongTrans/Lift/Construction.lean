module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Pseudofunctor
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

/-!
# Strong transformations between lifted pseudofunctors

An ambient strong transformation between arbitrary pseudofunctors lifts canonically when both
pseudofunctors take values in a fixed object property. The component and naturality data are
unchanged; only the full-subbicategory wrappers are added.
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

namespace Implementation.LiftPseudofunctor

variable (F G : Pseudofunctor A D)
variable (hF : ∀ X : A, P (F.obj X)) (hG : ∀ X : A, P (G.obj X))
variable (η : Pseudofunctor.StrongTrans F G)

/-- An ambient component regarded as a morphism in the selected full subbicategory. -/
private def app (X : A) :
    (FullSubbicategory.liftPseudofunctor F hF).obj X ⟶
      (FullSubbicategory.liftPseudofunctor G hG).obj X :=
  Bicategory.InducedBicategory.mkHom (η.app X)

/-- An ambient naturality isomorphism regarded in the selected full subbicategory. -/
private def naturality {X Y : A} (f : X ⟶ Y) :
    (FullSubbicategory.liftPseudofunctor F hF).map f ≫ app F G hF hG η Y ≅
      app F G hF hG η X ≫
        (FullSubbicategory.liftPseudofunctor G hG).map f :=
  Bicategory.InducedBicategory.isoMk (η.naturality f)

/-- Naturality in source `2`-morphisms for the lifted strong transformation. -/
private theorem naturality₂ :
    ∀ {X Y : A} {f g : X ⟶ Y} (θ : f ⟶ g),
      (FullSubbicategory.liftPseudofunctor F hF).map₂ θ ▷ app F G hF hG η Y ≫
          (naturality F G hF hG η g).hom =
        (naturality F G hF hG η f).hom ≫
          app F G hF hG η X ◁
            (FullSubbicategory.liftPseudofunctor G hG).map₂ θ := sorry

/-- Identity coherence for the lifted strong transformation. -/
private theorem naturalityId :
    ∀ X : A,
      (naturality F G hF hG η (𝟙 X)).hom ≫
          app F G hF hG η X ◁
            ((FullSubbicategory.liftPseudofunctor G hG).mapId X).hom =
        ((FullSubbicategory.liftPseudofunctor F hF).mapId X).hom ▷
            app F G hF hG η X ≫
          (λ_ (app F G hF hG η X)).hom ≫
          (ρ_ (app F G hF hG η X)).inv := sorry

/-- Composition coherence for the lifted strong transformation. -/
private theorem naturalityComp :
    ∀ {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z),
      (naturality F G hF hG η (f ≫ g)).hom ≫
          app F G hF hG η X ◁
            ((FullSubbicategory.liftPseudofunctor G hG).mapComp f g).hom =
        ((FullSubbicategory.liftPseudofunctor F hF).mapComp f g).hom ▷
            app F G hF hG η Z ≫
          (α_ _ _ _).hom ≫
          (FullSubbicategory.liftPseudofunctor F hF).map f ◁
            (naturality F G hF hG η g).hom ≫
          (α_ _ _ _).inv ≫
          (naturality F G hF hG η f).hom ▷
            (FullSubbicategory.liftPseudofunctor G hG).map g ≫
          (α_ _ _ _).hom := sorry

end Implementation.LiftPseudofunctor

/-- Lift a strong transformation between arbitrary ambient pseudofunctors through the full
subbicategory selected by `P`. The construction retains all ambient non-`Prop` data. -/
def liftPseudofunctor (F G : Pseudofunctor A D)
    (hF : ∀ X : A, P (F.obj X)) (hG : ∀ X : A, P (G.obj X))
    (η : Pseudofunctor.StrongTrans F G) :
    Pseudofunctor.StrongTrans
      (FullSubbicategory.liftPseudofunctor F hF)
      (FullSubbicategory.liftPseudofunctor G hG) where
  app := Implementation.LiftPseudofunctor.app F G hF hG η
  naturality := Implementation.LiftPseudofunctor.naturality F G hF hG η
  naturality_naturality := Implementation.LiftPseudofunctor.naturality₂ F G hF hG η
  naturality_id := Implementation.LiftPseudofunctor.naturalityId F G hF hG η
  naturality_comp := Implementation.LiftPseudofunctor.naturalityComp F G hF hG η

end ObjectProperty.FullSubbicategory.StrongTrans

end CategoryTheory
