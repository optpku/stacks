module

public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Left
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of pointwise left-derived values

This leaf constructs the map on an individual pointwise left-derived value induced by a
natural transformation.  It records the raw limit-projection formula, the denominator-facing
formula, and naturality in the source object without assuming global pointwise definedness.
-/

@[expose] public section

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.LeftDerived.Value

open Limits

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]

/-- The map on the pointwise left-derived value at `X` induced by `τ : F ⟶ G`. -/
@[stacks 05SA "pointwise left-derived value of a natural transformation"]
noncomputable def mapNatTrans.component (S : MorphismProperty C) {F G : C ⥤ D}
    (τ : F ⟶ G) (X : C) [F.HasPointwiseLeftDerivedFunctorAt S X]
    [G.HasPointwiseLeftDerivedFunctorAt S X] : obj F S X ⟶ obj G S X :=
  limMap (Functor.whiskerLeft
    (StructuredArrow.proj (S.Q.obj X) S.Q) τ)

/-- The component induced by `τ` commutes with every projection of the defining limit. -/
@[reassoc (attr := simp), stacks 05SA "pointwise left-derived transformation on limit projections"]
theorem mapNatTrans.component.π (S : MorphismProperty C) {F G : C ⥤ D}
    (τ : F ⟶ G) (X : C) [F.HasPointwiseLeftDerivedFunctorAt S X]
    [G.HasPointwiseLeftDerivedFunctorAt S X]
    (U : StructuredArrow (S.Q.obj X) S.Q) :
    mapNatTrans.component S τ X ≫
        limit.π (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ G) U =
      limit.π (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F) U ≫
        τ.app U.right := sorry

/-- On a denominator, the component induced by `τ` is computed directly using the
canonical pointwise left-derived projections. -/
@[reassoc (attr := simp), stacks 05SA "pointwise left-derived transformation on denominators"]
theorem mapNatTrans.component.π_denominator (S : MorphismProperty C) {F G : C ⥤ D}
    (τ : F ⟶ G) {X X' : C} (s : X' ⟶ X) (hs : S s)
    [F.HasPointwiseLeftDerivedFunctorAt S X]
    [G.HasPointwiseLeftDerivedFunctorAt S X] :
    mapNatTrans.component S τ X ≫
        CategoryTheory.Functor.LeftDerived.Value.π G S s hs =
      CategoryTheory.Functor.LeftDerived.Value.π F S s hs ≫ τ.app X' := sorry

/-- The component maps induced by `τ` are natural in the source object wherever the four
involved pointwise values exist. -/
@[reassoc (attr := simp), stacks 05SA "pointwise left-derived transformation naturality"]
theorem mapNatTrans.component.naturality (S : MorphismProperty C) {F G : C ⥤ D}
    (τ : F ⟶ G) {X Y : C} (f : X ⟶ Y)
    [F.HasPointwiseLeftDerivedFunctorAt S X]
    [F.HasPointwiseLeftDerivedFunctorAt S Y]
    [G.HasPointwiseLeftDerivedFunctorAt S X]
    [G.HasPointwiseLeftDerivedFunctorAt S Y] :
    map F S f ≫ mapNatTrans.component S τ Y =
      mapNatTrans.component S τ X ≫ map G S f := sorry

/-- The component construction sends the identity transformation to the identity map. -/
@[simp, stacks 05SA "pointwise left-derived component identity"]
theorem mapNatTrans.component.id (S : MorphismProperty C) (F : C ⥤ D) (X : C)
    [F.HasPointwiseLeftDerivedFunctorAt S X] :
    mapNatTrans.component S (𝟙 F) X = 𝟙 (obj F S X) := sorry

/-- The component construction preserves vertical composition of natural transformations. -/
@[simp, stacks 05SA "pointwise left-derived component composition"]
theorem mapNatTrans.component.comp (S : MorphismProperty C) {F G H : C ⥤ D}
    (τ : F ⟶ G) (σ : G ⟶ H) (X : C)
    [F.HasPointwiseLeftDerivedFunctorAt S X]
    [G.HasPointwiseLeftDerivedFunctorAt S X]
    [H.HasPointwiseLeftDerivedFunctorAt S X] :
    mapNatTrans.component S (τ ≫ σ) X =
      mapNatTrans.component S τ X ≫ mapNatTrans.component S σ X := sorry

/-- The pointwise left-derived value isomorphism at `X` induced by `e : F ≅ G`. -/
@[stacks 05SA "pointwise left-derived value of a natural isomorphism"]
noncomputable def mapNatIso.component (S : MorphismProperty C) {F G : C ⥤ D}
    (e : F ≅ G) (X : C) [F.HasPointwiseLeftDerivedFunctorAt S X]
    [G.HasPointwiseLeftDerivedFunctorAt S X] : obj F S X ≅ obj G S X :=
  HasLimit.isoOfNatIso (isoWhiskerLeft
    (StructuredArrow.proj (S.Q.obj X) S.Q) e)

/-- The forward map of the pointwise isomorphism is induced by `e.hom`. -/
@[simp, stacks 05SA "pointwise left-derived isomorphism forward component"]
theorem mapNatIso.component.hom (S : MorphismProperty C) {F G : C ⥤ D}
    (e : F ≅ G) (X : C) [F.HasPointwiseLeftDerivedFunctorAt S X]
    [G.HasPointwiseLeftDerivedFunctorAt S X] :
    (mapNatIso.component S e X).hom = mapNatTrans.component S e.hom X := sorry

/-- The inverse map of the pointwise isomorphism is induced by `e.inv`. -/
@[simp, stacks 05SA "pointwise left-derived isomorphism inverse component"]
theorem mapNatIso.component.inv (S : MorphismProperty C) {F G : C ⥤ D}
    (e : F ≅ G) (X : C) [F.HasPointwiseLeftDerivedFunctorAt S X]
    [G.HasPointwiseLeftDerivedFunctorAt S X] :
    (mapNatIso.component S e X).inv = mapNatTrans.component S e.inv X := sorry

/-- The pointwise isomorphisms induced by `e` are natural in the source object wherever the
four involved values exist. -/
@[reassoc (attr := simp), stacks 05SA "pointwise left-derived natural isomorphism naturality"]
theorem mapNatIso.component.naturality (S : MorphismProperty C) {F G : C ⥤ D}
    (e : F ≅ G) {X Y : C} (f : X ⟶ Y)
    [F.HasPointwiseLeftDerivedFunctorAt S X]
    [F.HasPointwiseLeftDerivedFunctorAt S Y]
    [G.HasPointwiseLeftDerivedFunctorAt S X]
    [G.HasPointwiseLeftDerivedFunctorAt S Y] :
    map F S f ≫ (mapNatIso.component S e Y).hom =
      (mapNatIso.component S e X).hom ≫ map G S f := sorry

/-- Inverse naturality of the pointwise isomorphisms induced by `e`, without assuming global
pointwise existence. -/
@[reassoc (attr := simp), stacks 05SA "pointwise left-derived inverse isomorphism naturality"]
theorem mapNatIso.component.inv_naturality (S : MorphismProperty C) {F G : C ⥤ D}
    (e : F ≅ G) {X Y : C} (f : X ⟶ Y)
    [F.HasPointwiseLeftDerivedFunctorAt S X]
    [F.HasPointwiseLeftDerivedFunctorAt S Y]
    [G.HasPointwiseLeftDerivedFunctorAt S X]
    [G.HasPointwiseLeftDerivedFunctorAt S Y] :
    map G S f ≫ (mapNatIso.component S e Y).inv =
      (mapNatIso.component S e X).inv ≫ map F S f := sorry

/-- The pointwise isomorphism construction sends reflexivity to reflexivity at each object. -/
@[simp, stacks 05SA "pointwise left-derived isomorphism identity"]
theorem mapNatIso.component.refl (S : MorphismProperty C) (F : C ⥤ D) (X : C)
    [F.HasPointwiseLeftDerivedFunctorAt S X] :
    mapNatIso.component S (Iso.refl F) X = Iso.refl (obj F S X) := sorry

/-- The pointwise isomorphism construction commutes with symmetry at each object. -/
@[simp, stacks 05SA "pointwise left-derived isomorphism symmetry"]
theorem mapNatIso.component.symm (S : MorphismProperty C) {F G : C ⥤ D}
    (e : F ≅ G) (X : C) [F.HasPointwiseLeftDerivedFunctorAt S X]
    [G.HasPointwiseLeftDerivedFunctorAt S X] :
    mapNatIso.component S e.symm X = (mapNatIso.component S e X).symm := sorry

/-- The pointwise isomorphism construction preserves transitivity at each object. -/
@[simp, stacks 05SA "pointwise left-derived isomorphism transitivity"]
theorem mapNatIso.component.trans (S : MorphismProperty C) {F G H : C ⥤ D}
    (e : F ≅ G) (e' : G ≅ H) (X : C)
    [F.HasPointwiseLeftDerivedFunctorAt S X]
    [G.HasPointwiseLeftDerivedFunctorAt S X]
    [H.HasPointwiseLeftDerivedFunctorAt S X] :
    mapNatIso.component S (e.trans e') X =
      (mapNatIso.component S e X).trans (mapNatIso.component S e' X) := sorry



end CategoryTheory.Functor.LeftDerived.Value
