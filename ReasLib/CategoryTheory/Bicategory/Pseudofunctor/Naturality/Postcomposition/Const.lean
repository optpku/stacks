module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Postcomposition.Pseudofunctor.Basic
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Constructions.Constant.Diagram
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Constructions.Constant.Map

/-!
# Constant diagrams and postcomposition

The canonical strong transformation comparing constant diagrams before and after
postcomposition by a pseudofunctor.
-/

@[expose] public section

universe wB vB uB wD vD uD wJ vJ uJ

namespace CategoryTheory

open scoped Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor

variable {B : Type uB} [Bicategory.{wB, vB} B]
  {D : Type uD} [Bicategory.{wD, vD} D]

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

section MapConstTransformation

variable {J : Type uJ} [Bicategory.{wJ, vJ} J]

namespace Implementation

/-- The pointwise isomorphism comparing the two ways to map a morphism between constant
diagrams and then apply the constant-diagram comparison. -/
private def transformationNaturalityApp
    (K : Pseudofunctor B D) {X Y : B} (f : X ⟶ Y) (j : J) :
    (((K.comp (constDiagram J D)).map f ≫ mapConst J K Y).app j) ≅
      ((mapConst J K X ≫
        ((constDiagram J B).comp (postcomp J K)).map f).app j) :=
  ρ_ (K.map f) ≪≫ (λ_ (K.map f)).symm

/-- The pointwise comparison for `mapConst` is natural in arrows of the diagram shape. -/
private theorem transformationNaturalityApp_naturality
    (K : Pseudofunctor B D) {X Y : B} (f : X ⟶ Y) :
    ∀ {j k : J} (h : j ⟶ k),
      (const J (K.obj X)).map h ◁
          (transformationNaturalityApp K f k).hom ≫
        ((mapConst J K X ≫
          ((constDiagram J B).comp (postcomp J K)).map f).naturality h).hom =
      (((K.comp (constDiagram J D)).map f ≫ mapConst J K Y).naturality h).hom ≫
        (transformationNaturalityApp K f j).hom ▷
          ((const J Y).comp K).map h := sorry
/- Proof strategy: expand `mapConst`, `constMap`, and postcomposition. The two pastings reduce to
naturality of the left and right unitors around `K.map f`, together with the identity and
composition coherence of `K`. -/

end Implementation

variable (J) in
/-- Naturality in the chosen object of the comparison from the constant diagram at `K.obj X`
to the image under `K` of the constant diagram at `X`.

At every object of the diagram shape, this is the canonical isomorphism
`K.map f ≫ 𝟙 _ ≅ 𝟙 _ ≫ K.map f`. -/
def mapConst.transformation.naturalityIso
    (K : Pseudofunctor B D) {X Y : B} (f : X ⟶ Y) :
    (K.comp (constDiagram J D)).map f ≫ mapConst J K Y ≅
      mapConst J K X ≫ ((constDiagram J B).comp (postcomp J K)).map f :=
  StrongTrans.isoMk
    (Implementation.transformationNaturalityApp K f)
    (Implementation.transformationNaturalityApp_naturality K f)

/-- The forward component of `mapConst.transformation.naturalityIso` is the right unitor followed
by the inverse left unitor. -/
@[simp]
theorem mapConst.transformation.naturalityIso.hom_app
    (K : Pseudofunctor B D) {X Y : B} (f : X ⟶ Y) (j : J) :
    (mapConst.transformation.naturalityIso J K f).hom.as.app j =
      (ρ_ (K.map f) ≪≫ (λ_ (K.map f)).symm).hom := sorry
/- Proof strategy: unfold `mapConst.transformation.naturalityIso` and `StrongTrans.isoMk`; read the
forward component of the explicitly supplied pointwise isomorphism. -/

/-- The inverse component of `mapConst.transformation.naturalityIso` is the left unitor followed
by the inverse right unitor. -/
@[simp]
theorem mapConst.transformation.naturalityIso.inv_app
    (K : Pseudofunctor B D) {X Y : B} (f : X ⟶ Y) (j : J) :
    (mapConst.transformation.naturalityIso J K f).inv.as.app j =
      (ρ_ (K.map f) ≪≫ (λ_ (K.map f)).symm).inv := sorry
/- Proof strategy: unfold `mapConst.transformation.naturalityIso` and `StrongTrans.isoMk`; read the
inverse component of the explicitly supplied pointwise isomorphism. -/

namespace Implementation

/-- Naturality of the objectwise constant-diagram comparison in `2`-morphisms of the chosen
object. -/
private theorem transformation_naturality_naturality
    (K : Pseudofunctor B D) :
    ∀ {X Y : B} {f g : X ⟶ Y} (η : f ⟶ g),
      (K.comp (constDiagram J D)).map₂ η ▷ mapConst J K Y ≫
          (mapConst.transformation.naturalityIso J K g).hom =
        (mapConst.transformation.naturalityIso J K f).hom ≫
          mapConst J K X ◁
            ((constDiagram J B).comp (postcomp J K)).map₂ η := sorry
/- Proof strategy: apply modification extensionality and evaluate at each `j : J`; the equation
is naturality of the unitors with respect to `K.map₂ η`. -/

/-- Identity coherence of the objectwise constant-diagram comparison. -/
private theorem transformation_naturality_id
    (K : Pseudofunctor B D) :
    ∀ X : B,
      (mapConst.transformation.naturalityIso J K (𝟙 X)).hom ≫
          mapConst J K X ◁
            (((constDiagram J B).comp (postcomp J K)).mapId X).hom =
        ((K.comp (constDiagram J D)).mapId X).hom ▷ mapConst J K X ≫
          (StrongTrans.leftUnitor (mapConst J K X)).hom ≫
            (StrongTrans.rightUnitor (mapConst J K X)).inv := sorry
/- Proof strategy: evaluate the modification equation at every `j : J`; expand the unit
comparisons of composition, `constDiagram`, and `postcomp`, then apply the identity coherence of
`K`. -/

/-- Composition coherence of the objectwise constant-diagram comparison. -/
private theorem transformation_naturality_comp
    (K : Pseudofunctor B D) :
    ∀ {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z),
      (mapConst.transformation.naturalityIso J K (f ≫ g)).hom ≫
          mapConst J K X ◁
            (((constDiagram J B).comp (postcomp J K)).mapComp f g).hom =
        ((K.comp (constDiagram J D)).mapComp f g).hom ▷ mapConst J K Z ≫
          (α_ _ _ _).hom ≫
          (K.comp (constDiagram J D)).map f ◁
            (mapConst.transformation.naturalityIso J K g).hom ≫
          (α_ _ _ _).inv ≫
          (mapConst.transformation.naturalityIso J K f).hom ▷
            ((constDiagram J B).comp (postcomp J K)).map g ≫
          (α_ _ _ _).hom := sorry
/- Proof strategy: apply modification extensionality and evaluate pointwise. The resulting
pasting is the composition coherence of `K` together with associator and unitor coherence. -/

end Implementation

variable (J) in
/-- The canonical strong transformation expressing that postcomposition by `K` preserves
constant diagrams up to the specified pseudofunctorial comparison.

Its component at `X` is `mapConst J K X`. This transformation is the shape-independent
naturality owner needed to map varying-apex conical pseudocones functorially. -/
def mapConst.transformation (K : Pseudofunctor B D) :
    StrongTrans
      (K.comp (constDiagram J D))
      ((constDiagram J B).comp (postcomp J K)) where
  app := mapConst J K
  naturality := mapConst.transformation.naturalityIso J K
  naturality_naturality :=
    Implementation.transformation_naturality_naturality K
  naturality_id := Implementation.transformation_naturality_id K
  naturality_comp := Implementation.transformation_naturality_comp K

/-- The component of `mapConst.transformation J K` at `X` is the canonical comparison
`mapConst J K X`. -/
@[simp]
theorem mapConst.transformation.app
    (K : Pseudofunctor B D) (X : B) :
    (mapConst.transformation J K).app X = mapConst J K X := sorry
/- Proof strategy: unfold `mapConst.transformation` and read its component field. -/

/-- Every diagram-object component of `mapConst.transformation J K` is an identity
`1`-morphism. -/
@[simp]
theorem mapConst.transformation.app_app
    (K : Pseudofunctor B D) (X : B) (j : J) :
    ((mapConst.transformation J K).app X).app j =
      𝟙 (K.obj X) := sorry
/- Proof strategy: rewrite with `mapConst.transformation.app` and `mapConst.app`. -/

/-- The internal naturality comparison at an arrow of the diagram shape is the comparison
stored by `mapConst`. -/
@[simp]
theorem mapConst.transformation.app_naturality
    (K : Pseudofunctor B D) (X : B) {j k : J} (h : j ⟶ k) :
    ((mapConst.transformation J K).app X).naturality h =
      λ_ (𝟙 (K.obj X)) ≪≫ (K.mapId X).symm ≪≫
        (λ_ (K.map (𝟙 X))).symm := sorry
/- Proof strategy: rewrite with `mapConst.transformation.app` and `mapConst.naturality`. -/

/-- The naturality isomorphism of `mapConst.transformation J K` is the explicit pointwise
unitor comparison. -/
@[simp]
theorem mapConst.transformation.naturality
    (K : Pseudofunctor B D) {X Y : B} (f : X ⟶ Y) :
    (mapConst.transformation J K).naturality f =
      mapConst.transformation.naturalityIso J K f := sorry
/- Proof strategy: unfold `mapConst.transformation` and read its naturality field. -/

/-- The forward pointwise component of the outer naturality comparison is the right unitor
followed by the inverse left unitor. -/
@[simp]
theorem mapConst.transformation.naturality.hom_app
    (K : Pseudofunctor B D) {X Y : B} (f : X ⟶ Y) (j : J) :
    ((mapConst.transformation J K).naturality f).hom.as.app j =
      (ρ_ (K.map f) ≪≫ (λ_ (K.map f)).symm).hom := sorry
/- Proof strategy: rewrite with `mapConst.transformation.naturality` and
`mapConst.transformation.naturalityIso.hom_app`. -/

/-- The inverse pointwise component of the outer naturality comparison is the left unitor
followed by the inverse right unitor. -/
@[simp]
theorem mapConst.transformation.naturality.inv_app
    (K : Pseudofunctor B D) {X Y : B} (f : X ⟶ Y) (j : J) :
    ((mapConst.transformation J K).naturality f).inv.as.app j =
      (ρ_ (K.map f) ≪≫ (λ_ (K.map f)).symm).inv := sorry
/- Proof strategy: rewrite with `mapConst.transformation.naturality` and
`mapConst.transformation.naturalityIso.inv_app`. -/

/- Data audit (mathlib 4.32): `mapConst.transformation` stores every strong-transformation
component and every naturality isomorphism explicitly. The forward and inverse modification
components of its naturality isomorphisms are unitors; any `sorryAx` is confined to
modification naturality and strong-transformation coherence equations. -/

end MapConstTransformation

end Pseudofunctor

end CategoryTheory
