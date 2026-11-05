module

public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Functor.Right
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Naturality.Right
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of the pointwise right-derived value functor

This file assembles the pointwise component construction into natural transformations and
natural isomorphisms under global pointwise definedness.
-/

@[expose] public section

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.RightDerived.Value

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]

/-- A natural transformation induces one between the pointwise right-derived value functors. -/
@[stacks 05SA "pointwise right-derived action on natural transformations"]
noncomputable def mapNatTrans (S : MorphismProperty C) {F G : C ⥤ D}
    (τ : F ⟶ G) [F.HasPointwiseRightDerivedFunctor S]
    [G.HasPointwiseRightDerivedFunctor S] : functor F S ⟶ functor G S where
  app X := mapNatTrans.component S τ X
  naturality := fun {_ _} f ↦ mapNatTrans.component.naturality S τ f

/-- Evaluation of the induced transformation is the canonical map of pointwise values. -/
@[simp, stacks 05SA "pointwise right-derived transformation component"]
theorem mapNatTrans.app (S : MorphismProperty C) {F G : C ⥤ D} (τ : F ⟶ G)
    [F.HasPointwiseRightDerivedFunctor S] [G.HasPointwiseRightDerivedFunctor S] (X : C) :
    (mapNatTrans S τ).app X = mapNatTrans.component S τ X := sorry

/-- Naturality of the induced transformation, exposed without unfolding its structure. -/
@[reassoc, stacks 05SA "pointwise right-derived transformation naturality"]
theorem mapNatTrans.naturality (S : MorphismProperty C) {F G : C ⥤ D}
    (τ : F ⟶ G) [F.HasPointwiseRightDerivedFunctor S]
    [G.HasPointwiseRightDerivedFunctor S] {X Y : C} (f : X ⟶ Y) :
    (functor F S).map f ≫ (mapNatTrans S τ).app Y =
      (mapNatTrans S τ).app X ≫ (functor G S).map f := sorry

/-- Pointwise right-derived values preserve identity natural transformations. -/
@[simp, stacks 05SA "pointwise right-derived transformation identity"]
theorem mapNatTrans.id (S : MorphismProperty C) (F : C ⥤ D)
    [F.HasPointwiseRightDerivedFunctor S] :
    mapNatTrans S (𝟙 F) = 𝟙 (functor F S) := sorry

/-- Pointwise right-derived values preserve vertical composition of natural transformations. -/
@[simp, stacks 05SA "pointwise right-derived transformation composition"]
theorem mapNatTrans.comp (S : MorphismProperty C) {F G H : C ⥤ D}
    (τ : F ⟶ G) (σ : G ⟶ H) [F.HasPointwiseRightDerivedFunctor S]
    [G.HasPointwiseRightDerivedFunctor S] [H.HasPointwiseRightDerivedFunctor S] :
    mapNatTrans S (τ ≫ σ) = mapNatTrans S τ ≫ mapNatTrans S σ := sorry

/-- A natural isomorphism induces one between the pointwise right-derived value functors. -/
@[stacks 05SA "pointwise right-derived action on natural isomorphisms"]
noncomputable def mapNatIso (S : MorphismProperty C) {F G : C ⥤ D}
    (e : F ≅ G) [F.HasPointwiseRightDerivedFunctor S]
    [G.HasPointwiseRightDerivedFunctor S] : functor F S ≅ functor G S :=
  NatIso.ofComponents (fun X ↦ mapNatIso.component S e X)
    (fun {_ _} f ↦ mapNatIso.component.naturality S e f)

/-- The forward transformation of `mapNatIso S e` is induced by `e.hom`. -/
@[simp, stacks 05SA "pointwise right-derived natural isomorphism forward map"]
theorem mapNatIso.hom (S : MorphismProperty C) {F G : C ⥤ D} (e : F ≅ G)
    [F.HasPointwiseRightDerivedFunctor S] [G.HasPointwiseRightDerivedFunctor S] :
    (mapNatIso S e).hom = mapNatTrans S e.hom := sorry

/-- The inverse transformation of `mapNatIso S e` is induced by `e.inv`. -/
@[simp, stacks 05SA "pointwise right-derived natural isomorphism inverse map"]
theorem mapNatIso.inv (S : MorphismProperty C) {F G : C ⥤ D} (e : F ≅ G)
    [F.HasPointwiseRightDerivedFunctor S] [G.HasPointwiseRightDerivedFunctor S] :
    (mapNatIso S e).inv = mapNatTrans S e.inv := sorry

/-- The forward component of the global isomorphism is the canonical pointwise isomorphism. -/
@[simp, stacks 05SA "pointwise right-derived natural isomorphism forward component"]
theorem mapNatIso.hom_app (S : MorphismProperty C) {F G : C ⥤ D} (e : F ≅ G)
    [F.HasPointwiseRightDerivedFunctor S] [G.HasPointwiseRightDerivedFunctor S] (X : C) :
    (mapNatIso S e).hom.app X = (mapNatIso.component S e X).hom := sorry

/-- The inverse component of the global isomorphism is the inverse pointwise isomorphism. -/
@[simp, stacks 05SA "pointwise right-derived natural isomorphism inverse component"]
theorem mapNatIso.inv_app (S : MorphismProperty C) {F G : C ⥤ D} (e : F ≅ G)
    [F.HasPointwiseRightDerivedFunctor S] [G.HasPointwiseRightDerivedFunctor S] (X : C) :
    (mapNatIso S e).inv.app X = (mapNatIso.component S e X).inv := sorry

/-- The pointwise right-derived action sends a reflexivity isomorphism to reflexivity. -/
@[simp, stacks 05SA "pointwise right-derived natural isomorphism identity"]
theorem mapNatIso.refl (S : MorphismProperty C) (F : C ⥤ D)
    [F.HasPointwiseRightDerivedFunctor S] :
    mapNatIso S (Iso.refl F) = Iso.refl (functor F S) := sorry

/-- The pointwise right-derived action commutes with symmetry of natural isomorphisms. -/
@[simp, stacks 05SA "pointwise right-derived natural isomorphism symmetry"]
theorem mapNatIso.symm (S : MorphismProperty C) {F G : C ⥤ D} (e : F ≅ G)
    [F.HasPointwiseRightDerivedFunctor S] [G.HasPointwiseRightDerivedFunctor S] :
    mapNatIso S e.symm = (mapNatIso S e).symm := sorry

/-- The pointwise right-derived action preserves transitivity of natural isomorphisms. -/
@[simp, stacks 05SA "pointwise right-derived natural isomorphism transitivity"]
theorem mapNatIso.trans (S : MorphismProperty C) {F G H : C ⥤ D}
    (e : F ≅ G) (e' : G ≅ H) [F.HasPointwiseRightDerivedFunctor S]
    [G.HasPointwiseRightDerivedFunctor S] [H.HasPointwiseRightDerivedFunctor S] :
    mapNatIso S (e.trans e') = (mapNatIso S e).trans (mapNatIso S e') := sorry



end CategoryTheory.Functor.RightDerived.Value
