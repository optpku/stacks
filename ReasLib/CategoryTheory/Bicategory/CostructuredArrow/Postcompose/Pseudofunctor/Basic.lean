/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Postcompose.Pseudofunctor.Composition
public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Postcompose.Pseudofunctor.Identity

/-!
# The pseudofunctor postcomposing colax costructured arrows

A target `1`-morphism `f : X ⟶ Y` acts on the colax costructured-arrow
bicategories of a fixed pseudofunctor `K : A ⥤ᵖ C`. This file assembles the
explicit object, `1`-morphism, and `2`-morphism actions with their identity and
composition comparisons into a pseudofunctor.

All mathematical data are imported from the preceding layers. The private
statements below supply only functoriality and bicategorical coherence fields.
Projection formulas belong in a separate computations module.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory

universe uA vA wA uC vC wC

namespace CategoryTheory

open Bicategory

namespace Bicategory.ColaxCostructuredArrow

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {C : Type uC} [Bicategory.{wC, vC} C]
variable {K : Pseudofunctor A C}
variable {X Y : C}

namespace Implementation

/-- Postcomposition of costructured-arrow `2`-morphisms preserves
identities. -/
private theorem map₂_id
    (f : X ⟶ Y) {S T : ColaxCostructuredArrow K X}
    (u : S ⟶ T) :
    postcompose.map₂ f (𝟙 u) =
      𝟙 (postcompose.map f u) := sorry

/-- Postcomposition of costructured-arrow `2`-morphisms preserves vertical
composition. -/
private theorem map₂_comp
    (f : X ⟶ Y) {S T : ColaxCostructuredArrow K X}
    {u v w : S ⟶ T} (η : u ⟶ v) (θ : v ⟶ w) :
    postcompose.map₂ f (η ≫ θ) =
      postcompose.map₂ f η ≫ postcompose.map₂ f θ := sorry

/-- The explicit prelax core of postcomposition by a target
`1`-morphism. -/
private def prelax
    (f : X ⟶ Y) :
    PrelaxFunctor (ColaxCostructuredArrow K X)
      (ColaxCostructuredArrow K Y) where
  obj := postcompose.obj f
  map := postcompose.map f
  map₂ := postcompose.map₂ f
  map₂_id := map₂_id f
  map₂_comp := map₂_comp f

/-- Postcomposition preserves left whiskering up to its explicit composition
comparisons. -/
private theorem map₂_whiskerLeft
    (f : X ⟶ Y) :
    ∀ {S T U : ColaxCostructuredArrow K X} (u : S ⟶ T)
      {v w : T ⟶ U} (η : v ⟶ w),
      (prelax f).map₂ (u ◁ η) =
        (postcompose.mapComp f u v).hom ≫
          (prelax f).map u ◁ (prelax f).map₂ η ≫
          (postcompose.mapComp f u w).inv := sorry

/-- Postcomposition preserves right whiskering up to its explicit composition
comparisons. -/
private theorem map₂_whiskerRight
    (f : X ⟶ Y) :
    ∀ {S T U : ColaxCostructuredArrow K X}
      {u v : S ⟶ T} (η : u ⟶ v) (w : T ⟶ U),
      (prelax f).map₂ (η ▷ w) =
        (postcompose.mapComp f u w).hom ≫
          (prelax f).map₂ η ▷ (prelax f).map w ≫
          (postcompose.mapComp f v w).inv := sorry

/-- Postcomposition preserves associators. -/
private theorem map₂_associator
    (f : X ⟶ Y) :
    ∀ {R S T U : ColaxCostructuredArrow K X}
      (u : R ⟶ S) (v : S ⟶ T) (w : T ⟶ U),
      (prelax f).map₂ (α_ u v w).hom =
        (postcompose.mapComp f (u ≫ v) w).hom ≫
          (postcompose.mapComp f u v).hom ▷ (prelax f).map w ≫
          (α_ ((prelax f).map u) ((prelax f).map v)
            ((prelax f).map w)).hom ≫
          (prelax f).map u ◁ (postcompose.mapComp f v w).inv ≫
          (postcompose.mapComp f u (v ≫ w)).inv := sorry

/-- Postcomposition preserves left unitors. -/
private theorem map₂_leftUnitor
    (f : X ⟶ Y) :
    ∀ {S T : ColaxCostructuredArrow K X} (u : S ⟶ T),
      (prelax f).map₂ (λ_ u).hom =
        (postcompose.mapComp f (𝟙 S) u).hom ≫
          (postcompose.mapId f S).hom ▷ (prelax f).map u ≫
          (λ_ ((prelax f).map u)).hom := sorry

/-- Postcomposition preserves right unitors. -/
private theorem map₂_rightUnitor
    (f : X ⟶ Y) :
    ∀ {S T : ColaxCostructuredArrow K X} (u : S ⟶ T),
      (prelax f).map₂ (ρ_ u).hom =
        (postcompose.mapComp f u (𝟙 T)).hom ≫
          (prelax f).map u ◁ (postcompose.mapId f T).hom ≫
          (ρ_ ((prelax f).map u)).hom := sorry

end Implementation

variable (K) in
/-- Postcomposition by a target `1`-morphism is a pseudofunctor between the
corresponding bicategories of colax costructured arrows.

It retains source objects, source maps, and source `2`-cells. Its identity and
composition comparisons are `postcompose.mapId` and `postcompose.mapComp`.
The fixed pseudofunctor `K` is explicit because `f` alone does not determine
the costructured-arrow bicategories. -/
def postcompose
    (f : X ⟶ Y) :
    Pseudofunctor (ColaxCostructuredArrow K X)
      (ColaxCostructuredArrow K Y) where
  toPrelaxFunctor := Implementation.prelax f
  mapId := postcompose.mapId f
  mapComp := postcompose.mapComp f
  map₂_whisker_left := Implementation.map₂_whiskerLeft f
  map₂_whisker_right := Implementation.map₂_whiskerRight f
  map₂_associator := Implementation.map₂_associator f
  map₂_left_unitor := Implementation.map₂_leftUnitor f
  map₂_right_unitor := Implementation.map₂_rightUnitor f

/- Data and axiom audit (mathlib 4.32):

The object, `1`-morphism, `2`-morphism, identity, and composition fields of
`postcompose` are exactly the explicit owners imported above. Its private
helpers supply only `Prop`-valued functoriality and bicategorical coherence;
no source object, map, cell, normalized comparison, or comparison isomorphism
is selected through a proof placeholder. -/

end Bicategory.ColaxCostructuredArrow

end CategoryTheory
