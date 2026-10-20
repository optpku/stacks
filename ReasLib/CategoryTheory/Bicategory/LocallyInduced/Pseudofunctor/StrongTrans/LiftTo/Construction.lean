module

public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Iso
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Lift
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Pseudofunctor
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
import Mathlib.Tactic.CrossRefAttribute

/-!
# Strong transformations from locally induced pseudofunctor lifts

An ambient strong transformation from a pseudofunctor `G` to the canonical inclusion of an
already locally induced pseudofunctor `H` lifts to a strong transformation from
`LocallyInducedBicategory.liftPseudofunctor G` directly to `H`. This is the pseudofunctorial
counterpart of the strict identity-target construction and avoids rebuilding target comparison
data in applications.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

universe w v u uB wA vA uA

namespace CategoryTheory.Bicategory.LocallyInducedBicategory

open CategoryTheory ObjectProperty
open scoped CategoryTheory.Bicategory

variable {B : Type uB}
variable {D : Type u} [Bicategory.{w, v} D]
variable {F : B → D} {Q : HomProperty F} [Q.IsMultiplicative]
variable {A : Type uA} [Bicategory.{wA, vA} A]

namespace StrongTrans

namespace Implementation.LiftTo

variable (G : Pseudofunctor A (InducedBicategory D F))
variable (H : Pseudofunctor A (LocallyInducedBicategory D F Q))
variable (map_mem : ∀ {X Y : A} (f : X ⟶ Y),
  Q (G.obj X) (G.obj Y) (G.map f).hom)
variable (η : Pseudofunctor.StrongTrans G
  (H.comp (LocallyInducedBicategory.ι D F Q).toPseudofunctor))
variable (app_mem : ∀ X : A, Q (G.obj X) (H.obj X) (η.app X).hom)

/-- An ambient component satisfying `Q`, bundled as a locally induced morphism to the
prescribed target component. -/
private def component (X : A) :
    (liftPseudofunctor G map_mem).obj X ⟶ H.obj X :=
  mkHom (η.app X).hom (app_mem X)

/-- Ambient naturality bundled in the locally induced hom category. -/
private def naturalityIso {X Y : A} (f : X ⟶ Y) :
    (liftPseudofunctor G map_mem).map f ≫
        component G H map_mem η app_mem Y ≅
      component G H map_mem η app_mem X ≫ H.map f :=
  (Q _ _).isoMk (InducedBicategory.Iso.toAmbient (η.naturality f))

/-- Naturality in source `2`-cells for the lifted transformation. -/
private theorem naturality₂
    {X Y : A} {f g : X ⟶ Y} (τ : f ⟶ g) :
    (liftPseudofunctor G map_mem).map₂ τ ▷
          component G H map_mem η app_mem Y ≫
        (naturalityIso G H map_mem η app_mem g).hom =
      (naturalityIso G H map_mem η app_mem f).hom ≫
        component G H map_mem η app_mem X ◁ H.map₂ τ := sorry

/-- Identity coherence for the lifted transformation. -/
private theorem naturalityId (X : A) :
    (naturalityIso G H map_mem η app_mem (𝟙 X)).hom ≫
          component G H map_mem η app_mem X ◁ (H.mapId X).hom =
      ((liftPseudofunctor G map_mem).mapId X).hom ▷
          component G H map_mem η app_mem X ≫
        (λ_ (component G H map_mem η app_mem X)).hom ≫
        (ρ_ (component G H map_mem η app_mem X)).inv := sorry

/-- Composition coherence for the lifted transformation. -/
private theorem naturalityComp
    {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (naturalityIso G H map_mem η app_mem (f ≫ g)).hom ≫
          component G H map_mem η app_mem X ◁ (H.mapComp f g).hom =
      ((liftPseudofunctor G map_mem).mapComp f g).hom ▷
          component G H map_mem η app_mem Z ≫
        (α_ _ _ _).hom ≫
        (liftPseudofunctor G map_mem).map f ◁
          (naturalityIso G H map_mem η app_mem g).hom ≫
        (α_ _ _ _).inv ≫
        (naturalityIso G H map_mem η app_mem f).hom ▷ H.map g ≫
        (α_ _ _ _).hom := sorry

end Implementation.LiftTo

/-- Lift an ambient strong transformation to an already locally induced target
pseudofunctor. The construction retains the target pseudofunctor exactly and adds only the
source map-membership and component-membership witnesses. -/
@[stacks 0040 "lift an ambient transformation to a locally induced pseudofunctor"]
def liftTo
    (G : Pseudofunctor A (InducedBicategory D F))
    (H : Pseudofunctor A (LocallyInducedBicategory D F Q))
    (map_mem : ∀ {X Y : A} (f : X ⟶ Y),
      Q (G.obj X) (G.obj Y) (G.map f).hom)
    (η : Pseudofunctor.StrongTrans G
      (H.comp (LocallyInducedBicategory.ι D F Q).toPseudofunctor))
    (app_mem : ∀ X : A, Q (G.obj X) (H.obj X) (η.app X).hom) :
    Pseudofunctor.StrongTrans (liftPseudofunctor G map_mem) H where
  app := Implementation.LiftTo.component G H map_mem η app_mem
  naturality := Implementation.LiftTo.naturalityIso G H map_mem η app_mem
  naturality_naturality := Implementation.LiftTo.naturality₂ G H map_mem η app_mem
  naturality_id := Implementation.LiftTo.naturalityId G H map_mem η app_mem
  naturality_comp := Implementation.LiftTo.naturalityComp G H map_mem η app_mem

end StrongTrans

end CategoryTheory.Bicategory.LocallyInducedBicategory
