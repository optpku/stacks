/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Naturality of Total Right-Derived Functors

This file specializes Mathlib's universal naturality construction to the chosen total
right-derived functors.  The localization, inverted class, and source transformation are the
only explicit inputs needed by downstream users.
-/

noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.RightDerived

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]

/-- The map between chosen total right-derived functors induced by a natural transformation. -/
noncomputable def mapNatTrans
    (L : C ⥤ D) (S : MorphismProperty C) {F G : C ⥤ E} (τ : F ⟶ G)
    [L.IsLocalization S] [F.HasRightDerivedFunctor S] [G.HasRightDerivedFunctor S] :
    F.totalRightDerived L S ⟶ G.totalRightDerived L S :=
  Functor.rightDerivedNatTrans
    (F.totalRightDerived L S) (G.totalRightDerived L S)
    (F.totalRightDerivedUnit L S) (G.totalRightDerivedUnit L S) S τ

/-- The right-derived map is characterized by compatibility with the total derived units. -/
@[reassoc (attr := simp)]
theorem mapNatTrans.fac
    (L : C ⥤ D) (S : MorphismProperty C) {F G : C ⥤ E} (τ : F ⟶ G)
    [L.IsLocalization S] [F.HasRightDerivedFunctor S] [G.HasRightDerivedFunctor S] :
    F.totalRightDerivedUnit L S ≫ whiskerLeft L (mapNatTrans L S τ) =
      τ ≫ G.totalRightDerivedUnit L S := by
  exact Functor.rightDerivedNatTrans_fac _ _ _ _ S τ

/-- Objectwise compatibility of the right-derived map with the total derived units. -/
@[reassoc (attr := simp)]
theorem mapNatTrans.fac_app
    (L : C ⥤ D) (S : MorphismProperty C) {F G : C ⥤ E} (τ : F ⟶ G)
    [L.IsLocalization S] [F.HasRightDerivedFunctor S] [G.HasRightDerivedFunctor S] (X : C) :
    (F.totalRightDerivedUnit L S).app X ≫ (mapNatTrans L S τ).app (L.obj X) =
      τ.app X ≫ (G.totalRightDerivedUnit L S).app X := by
  exact Functor.rightDerivedNatTrans_app _ _ _ _ S τ X

/-- The total right-derived map induced by an identity transformation is the identity. -/
@[simp]
theorem mapNatTrans.id
    (L : C ⥤ D) (S : MorphismProperty C) (F : C ⥤ E)
    [L.IsLocalization S] [F.HasRightDerivedFunctor S] :
    mapNatTrans L S (𝟙 F) = 𝟙 (F.totalRightDerived L S) := by
  exact Functor.rightDerivedNatTrans_id _ _ S

/-- Total right-derived maps preserve composition of source natural transformations. -/
@[simp]
theorem mapNatTrans.comp
    (L : C ⥤ D) (S : MorphismProperty C) {F G K : C ⥤ E}
    (τ : F ⟶ G) (σ : G ⟶ K) [L.IsLocalization S]
    [F.HasRightDerivedFunctor S] [G.HasRightDerivedFunctor S]
    [K.HasRightDerivedFunctor S] :
    mapNatTrans L S (τ ≫ σ) = mapNatTrans L S τ ≫ mapNatTrans L S σ := by
  exact (Functor.rightDerivedNatTrans_comp _ _ _ _ _ _ S τ σ).symm

/- An invertible natural transformation is enough to expose the corresponding derived
invertibility without forcing callers to manufacture an `Iso`. -/
/-- A total right-derived map induced by an invertible natural transformation is invertible. -/
theorem mapNatTrans_isIso
    (L : C ⥤ D) (S : MorphismProperty C) {F G : C ⥤ E} (τ : F ⟶ G)
    [L.IsLocalization S] [F.HasRightDerivedFunctor S] [G.HasRightDerivedFunctor S]
    [IsIso τ] :
    IsIso (mapNatTrans L S τ) := by
  exact (Functor.rightDerivedNatIso
    (F.totalRightDerived L S) (G.totalRightDerived L S)
    (F.totalRightDerivedUnit L S) (G.totalRightDerivedUnit L S) S
    (asIso τ)).isIso_hom

/-- The isomorphism between chosen total right-derived functors induced by a natural
isomorphism. -/
noncomputable def mapNatIso
    (L : C ⥤ D) (S : MorphismProperty C) {F G : C ⥤ E} (e : F ≅ G)
    [L.IsLocalization S] [F.HasRightDerivedFunctor S] [G.HasRightDerivedFunctor S] :
    F.totalRightDerived L S ≅ G.totalRightDerived L S :=
  Functor.rightDerivedNatIso
    (F.totalRightDerived L S) (G.totalRightDerived L S)
    (F.totalRightDerivedUnit L S) (G.totalRightDerivedUnit L S) S e

/-- The hom of the induced total right-derived isomorphism is `mapNatTrans` on the hom. -/
@[simp]
theorem mapNatIso.hom
    (L : C ⥤ D) (S : MorphismProperty C) {F G : C ⥤ E} (e : F ≅ G)
    [L.IsLocalization S] [F.HasRightDerivedFunctor S] [G.HasRightDerivedFunctor S] :
    (mapNatIso L S e).hom = mapNatTrans L S e.hom := by
  rfl

/-- The inverse of the induced total right-derived isomorphism is `mapNatTrans` on the inverse. -/
@[simp]
theorem mapNatIso.inv
    (L : C ⥤ D) (S : MorphismProperty C) {F G : C ⥤ E} (e : F ≅ G)
    [L.IsLocalization S] [F.HasRightDerivedFunctor S] [G.HasRightDerivedFunctor S] :
    (mapNatIso L S e).inv = mapNatTrans L S e.inv := by
  rfl

/-- Total right-derived natural isomorphisms preserve reflexivity. -/
@[simp]
theorem mapNatIso.refl
    (L : C ⥤ D) (S : MorphismProperty C) (F : C ⥤ E)
    [L.IsLocalization S] [F.HasRightDerivedFunctor S] :
    mapNatIso L S (Iso.refl F) = Iso.refl (F.totalRightDerived L S) := by
  apply Iso.ext
  exact mapNatTrans.id L S F

/-- Total right-derived natural isomorphisms preserve symmetry. -/
@[simp]
theorem mapNatIso.symm
    (L : C ⥤ D) (S : MorphismProperty C) {F G : C ⥤ E} (e : F ≅ G)
    [L.IsLocalization S] [F.HasRightDerivedFunctor S] [G.HasRightDerivedFunctor S] :
    mapNatIso L S e.symm = (mapNatIso L S e).symm := by
  apply Iso.ext
  rfl

/-- Total right-derived natural isomorphisms preserve transitivity. -/
@[simp]
theorem mapNatIso.trans
    (L : C ⥤ D) (S : MorphismProperty C) {F G K : C ⥤ E}
    (e : F ≅ G) (e' : G ≅ K) [L.IsLocalization S]
    [F.HasRightDerivedFunctor S] [G.HasRightDerivedFunctor S]
    [K.HasRightDerivedFunctor S] :
    mapNatIso L S (e ≪≫ e') = mapNatIso L S e ≪≫ mapNatIso L S e' := by
  apply Iso.ext
  exact mapNatTrans.comp L S e.hom e'.hom



end CategoryTheory.Functor.RightDerived
