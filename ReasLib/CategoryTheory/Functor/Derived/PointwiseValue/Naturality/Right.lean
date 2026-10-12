/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Right
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of pointwise right-derived values

This leaf constructs the map on an individual pointwise right-derived value induced by a
natural transformation.  It records the raw colimit-leg formula, the denominator-facing
formula, and naturality in the source object without assuming global pointwise definedness.
-/

@[expose] public section

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.RightDerived.Value

open Limits

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]

/-- The map on the pointwise right-derived value at `X` induced by `τ : F ⟶ G`. -/
@[stacks 05SA "pointwise right-derived value of a natural transformation"]
noncomputable def mapNatTrans.component (S : MorphismProperty C) {F G : C ⥤ D}
    (τ : F ⟶ G) (X : C) [F.HasPointwiseRightDerivedFunctorAt S X]
    [G.HasPointwiseRightDerivedFunctorAt S X] : obj F S X ⟶ obj G S X :=
  colimMap (Functor.whiskerLeft
    (CostructuredArrow.proj S.Q (S.Q.obj X)) τ)

/-- The component induced by `τ` sends every source colimit leg to the corresponding target
leg after applying `τ`. -/
@[reassoc (attr := simp), stacks 05SA "pointwise right-derived transformation on colimit legs"]
theorem mapNatTrans.component.ι (S : MorphismProperty C) {F G : C ⥤ D}
    (τ : F ⟶ G) (X : C) [F.HasPointwiseRightDerivedFunctorAt S X]
    [G.HasPointwiseRightDerivedFunctorAt S X]
    (U : CostructuredArrow S.Q (S.Q.obj X)) :
    colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F) U ≫
        mapNatTrans.component S τ X =
      τ.app U.left ≫
        colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ G) U := sorry

/-- On a denominator, the component induced by `τ` is computed directly using the
canonical pointwise right-derived legs. -/
@[reassoc (attr := simp), stacks 05SA "pointwise right-derived transformation on denominators"]
theorem mapNatTrans.component.ι_denominator (S : MorphismProperty C) {F G : C ⥤ D}
    (τ : F ⟶ G) {X X' : C} (s : X ⟶ X') (hs : S s)
    [F.HasPointwiseRightDerivedFunctorAt S X]
    [G.HasPointwiseRightDerivedFunctorAt S X] :
    CategoryTheory.Functor.RightDerived.Value.ι F S s hs ≫
        mapNatTrans.component S τ X =
      τ.app X' ≫ CategoryTheory.Functor.RightDerived.Value.ι G S s hs := sorry

/-- The component maps induced by `τ` are natural in the source object wherever the four
involved pointwise values exist. -/
@[reassoc (attr := simp), stacks 05SA "pointwise right-derived transformation naturality"]
theorem mapNatTrans.component.naturality (S : MorphismProperty C) {F G : C ⥤ D}
    (τ : F ⟶ G) {X Y : C} (f : X ⟶ Y)
    [F.HasPointwiseRightDerivedFunctorAt S X]
    [F.HasPointwiseRightDerivedFunctorAt S Y]
    [G.HasPointwiseRightDerivedFunctorAt S X]
    [G.HasPointwiseRightDerivedFunctorAt S Y] :
    map F S f ≫ mapNatTrans.component S τ Y =
      mapNatTrans.component S τ X ≫ map G S f := sorry

/-- The component construction sends the identity transformation to the identity map. -/
@[simp, stacks 05SA "pointwise right-derived component identity"]
theorem mapNatTrans.component.id (S : MorphismProperty C) (F : C ⥤ D) (X : C)
    [F.HasPointwiseRightDerivedFunctorAt S X] :
    mapNatTrans.component S (𝟙 F) X = 𝟙 (obj F S X) := sorry

/-- The component construction preserves vertical composition of natural transformations. -/
@[simp, stacks 05SA "pointwise right-derived component composition"]
theorem mapNatTrans.component.comp (S : MorphismProperty C) {F G H : C ⥤ D}
    (τ : F ⟶ G) (σ : G ⟶ H) (X : C)
    [F.HasPointwiseRightDerivedFunctorAt S X]
    [G.HasPointwiseRightDerivedFunctorAt S X]
    [H.HasPointwiseRightDerivedFunctorAt S X] :
    mapNatTrans.component S (τ ≫ σ) X =
      mapNatTrans.component S τ X ≫ mapNatTrans.component S σ X := sorry

/-- The pointwise right-derived value isomorphism at `X` induced by `e : F ≅ G`. -/
@[stacks 05SA "pointwise right-derived value of a natural isomorphism"]
noncomputable def mapNatIso.component (S : MorphismProperty C) {F G : C ⥤ D}
    (e : F ≅ G) (X : C) [F.HasPointwiseRightDerivedFunctorAt S X]
    [G.HasPointwiseRightDerivedFunctorAt S X] : obj F S X ≅ obj G S X :=
  HasColimit.isoOfNatIso (isoWhiskerLeft
    (CostructuredArrow.proj S.Q (S.Q.obj X)) e)

/-- The forward map of the pointwise isomorphism is induced by `e.hom`. -/
@[simp, stacks 05SA "pointwise right-derived isomorphism forward component"]
theorem mapNatIso.component.hom (S : MorphismProperty C) {F G : C ⥤ D}
    (e : F ≅ G) (X : C) [F.HasPointwiseRightDerivedFunctorAt S X]
    [G.HasPointwiseRightDerivedFunctorAt S X] :
    (mapNatIso.component S e X).hom = mapNatTrans.component S e.hom X := sorry

/-- The inverse map of the pointwise isomorphism is induced by `e.inv`. -/
@[simp, stacks 05SA "pointwise right-derived isomorphism inverse component"]
theorem mapNatIso.component.inv (S : MorphismProperty C) {F G : C ⥤ D}
    (e : F ≅ G) (X : C) [F.HasPointwiseRightDerivedFunctorAt S X]
    [G.HasPointwiseRightDerivedFunctorAt S X] :
    (mapNatIso.component S e X).inv = mapNatTrans.component S e.inv X := sorry

/-- The pointwise isomorphisms induced by `e` are natural in the source object wherever the
four involved values exist. -/
@[reassoc (attr := simp), stacks 05SA "pointwise right-derived natural isomorphism naturality"]
theorem mapNatIso.component.naturality (S : MorphismProperty C) {F G : C ⥤ D}
    (e : F ≅ G) {X Y : C} (f : X ⟶ Y)
    [F.HasPointwiseRightDerivedFunctorAt S X]
    [F.HasPointwiseRightDerivedFunctorAt S Y]
    [G.HasPointwiseRightDerivedFunctorAt S X]
    [G.HasPointwiseRightDerivedFunctorAt S Y] :
    map F S f ≫ (mapNatIso.component S e Y).hom =
      (mapNatIso.component S e X).hom ≫ map G S f := sorry

/-- Inverse naturality of the pointwise isomorphisms induced by `e`, without assuming global
pointwise existence. -/
@[reassoc (attr := simp), stacks 05SA "pointwise right-derived inverse isomorphism naturality"]
theorem mapNatIso.component.inv_naturality (S : MorphismProperty C) {F G : C ⥤ D}
    (e : F ≅ G) {X Y : C} (f : X ⟶ Y)
    [F.HasPointwiseRightDerivedFunctorAt S X]
    [F.HasPointwiseRightDerivedFunctorAt S Y]
    [G.HasPointwiseRightDerivedFunctorAt S X]
    [G.HasPointwiseRightDerivedFunctorAt S Y] :
    map G S f ≫ (mapNatIso.component S e Y).inv =
      (mapNatIso.component S e X).inv ≫ map F S f := sorry

/-- The pointwise isomorphism construction sends reflexivity to reflexivity at each object. -/
@[simp, stacks 05SA "pointwise right-derived isomorphism identity"]
theorem mapNatIso.component.refl (S : MorphismProperty C) (F : C ⥤ D) (X : C)
    [F.HasPointwiseRightDerivedFunctorAt S X] :
    mapNatIso.component S (Iso.refl F) X = Iso.refl (obj F S X) := sorry

/-- The pointwise isomorphism construction commutes with symmetry at each object. -/
@[simp, stacks 05SA "pointwise right-derived isomorphism symmetry"]
theorem mapNatIso.component.symm (S : MorphismProperty C) {F G : C ⥤ D}
    (e : F ≅ G) (X : C) [F.HasPointwiseRightDerivedFunctorAt S X]
    [G.HasPointwiseRightDerivedFunctorAt S X] :
    mapNatIso.component S e.symm X = (mapNatIso.component S e X).symm := sorry

/-- The pointwise isomorphism construction preserves transitivity at each object. -/
@[simp, stacks 05SA "pointwise right-derived isomorphism transitivity"]
theorem mapNatIso.component.trans (S : MorphismProperty C) {F G H : C ⥤ D}
    (e : F ≅ G) (e' : G ≅ H) (X : C)
    [F.HasPointwiseRightDerivedFunctorAt S X]
    [G.HasPointwiseRightDerivedFunctorAt S X]
    [H.HasPointwiseRightDerivedFunctorAt S X] :
    mapNatIso.component S (e.trans e') X =
      (mapNatIso.component S e X).trans (mapNatIso.component S e' X) := sorry



end CategoryTheory.Functor.RightDerived.Value
