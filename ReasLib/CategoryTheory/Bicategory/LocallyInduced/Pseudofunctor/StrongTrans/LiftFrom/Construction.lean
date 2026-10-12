/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Iso
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Lift
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Pseudofunctor
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
import Mathlib.Tactic.CrossRefAttribute

/-!
# Strong transformations to locally induced pseudofunctor lifts

An ambient strong transformation from the canonical inclusion of an already locally induced
pseudofunctor `G` to a pseudofunctor `H` lifts to a strong transformation from `G` directly to
`LocallyInducedBicategory.liftPseudofunctor H`. This is the source-preserving counterpart of
`StrongTrans.liftTo`.
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

namespace Implementation.LiftFrom

variable (G : Pseudofunctor A (LocallyInducedBicategory D F Q))
variable (H : Pseudofunctor A (InducedBicategory D F))
variable (map_mem : ∀ {X Y : A} (f : X ⟶ Y),
  Q (H.obj X) (H.obj Y) (H.map f).hom)
variable (η : Pseudofunctor.StrongTrans
  (G.comp (LocallyInducedBicategory.ι D F Q).toPseudofunctor) H)
variable (app_mem : ∀ X : A, Q (G.obj X) (H.obj X) (η.app X).hom)

/-- An ambient component satisfying `Q`, bundled as a locally induced morphism from the
prescribed source component. -/
private def component (X : A) :
    G.obj X ⟶ (liftPseudofunctor H map_mem).obj X :=
  mkHom (η.app X).hom (app_mem X)

/-- Ambient naturality bundled in the locally induced hom category. -/
private def naturalityIso {X Y : A} (f : X ⟶ Y) :
    G.map f ≫ component G H map_mem η app_mem Y ≅
      component G H map_mem η app_mem X ≫
        (liftPseudofunctor H map_mem).map f :=
  (Q _ _).isoMk (InducedBicategory.Iso.toAmbient (η.naturality f))

/-- Naturality in source `2`-cells for the source-preserving lifted transformation. -/
private theorem naturality₂
    {X Y : A} {f g : X ⟶ Y} (τ : f ⟶ g) :
    G.map₂ τ ▷ component G H map_mem η app_mem Y ≫
        (naturalityIso G H map_mem η app_mem g).hom =
      (naturalityIso G H map_mem η app_mem f).hom ≫
        component G H map_mem η app_mem X ◁
          (liftPseudofunctor H map_mem).map₂ τ := sorry

/-- Identity coherence for the source-preserving lifted transformation. -/
private theorem naturalityId (X : A) :
    (naturalityIso G H map_mem η app_mem (𝟙 X)).hom ≫
        component G H map_mem η app_mem X ◁
          ((liftPseudofunctor H map_mem).mapId X).hom =
      (G.mapId X).hom ▷ component G H map_mem η app_mem X ≫
        (λ_ (component G H map_mem η app_mem X)).hom ≫
        (ρ_ (component G H map_mem η app_mem X)).inv := sorry

/-- Composition coherence for the source-preserving lifted transformation. -/
private theorem naturalityComp
    {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (naturalityIso G H map_mem η app_mem (f ≫ g)).hom ≫
        component G H map_mem η app_mem X ◁
          ((liftPseudofunctor H map_mem).mapComp f g).hom =
      (G.mapComp f g).hom ▷ component G H map_mem η app_mem Z ≫
        (α_ _ _ _).hom ≫
        G.map f ◁ (naturalityIso G H map_mem η app_mem g).hom ≫
        (α_ _ _ _).inv ≫
        (naturalityIso G H map_mem η app_mem f).hom ▷
          (liftPseudofunctor H map_mem).map g ≫
        (α_ _ _ _).hom := sorry

end Implementation.LiftFrom

/-- Lift an ambient strong transformation from an already locally induced source
pseudofunctor. The construction retains the source pseudofunctor exactly and adds only the
target map-membership and component-membership witnesses. -/
@[stacks 0040 "lift an ambient transformation from a locally induced pseudofunctor"]
def liftFrom
    (G : Pseudofunctor A (LocallyInducedBicategory D F Q))
    (H : Pseudofunctor A (InducedBicategory D F))
    (map_mem : ∀ {X Y : A} (f : X ⟶ Y),
      Q (H.obj X) (H.obj Y) (H.map f).hom)
    (η : Pseudofunctor.StrongTrans
      (G.comp (LocallyInducedBicategory.ι D F Q).toPseudofunctor) H)
    (app_mem : ∀ X : A, Q (G.obj X) (H.obj X) (η.app X).hom) :
    Pseudofunctor.StrongTrans G (liftPseudofunctor H map_mem) where
  app := Implementation.LiftFrom.component G H map_mem η app_mem
  naturality := Implementation.LiftFrom.naturalityIso G H map_mem η app_mem
  naturality_naturality := Implementation.LiftFrom.naturality₂ G H map_mem η app_mem
  naturality_id := Implementation.LiftFrom.naturalityId G H map_mem η app_mem
  naturality_comp := Implementation.LiftFrom.naturalityComp G H map_mem η app_mem

end StrongTrans

end CategoryTheory.Bicategory.LocallyInducedBicategory
