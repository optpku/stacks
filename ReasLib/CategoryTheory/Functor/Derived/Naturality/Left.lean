/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Naturality of Total Left-Derived Functors

This file specializes Mathlib's universal naturality construction to the chosen total
left-derived functors.  The localization, inverted class, and source transformation are the only
explicit inputs needed by downstream users.
-/

noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.LeftDerived

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]

/-- The map between chosen total left-derived functors induced by a natural transformation. -/
noncomputable def mapNatTrans
    (L : C ⥤ D) (S : MorphismProperty C) {F G : C ⥤ E} (τ : F ⟶ G)
    [L.IsLocalization S] [F.HasLeftDerivedFunctor S] [G.HasLeftDerivedFunctor S] :
    F.totalLeftDerived L S ⟶ G.totalLeftDerived L S :=
  Functor.leftDerivedNatTrans
    (F.totalLeftDerived L S) (G.totalLeftDerived L S)
    (F.totalLeftDerivedCounit L S) (G.totalLeftDerivedCounit L S) S τ

/-- The left-derived map is characterized by compatibility with the total derived counits. -/
@[reassoc (attr := simp)]
theorem mapNatTrans.fac
    (L : C ⥤ D) (S : MorphismProperty C) {F G : C ⥤ E} (τ : F ⟶ G)
    [L.IsLocalization S] [F.HasLeftDerivedFunctor S] [G.HasLeftDerivedFunctor S] :
    whiskerLeft L (mapNatTrans L S τ) ≫ G.totalLeftDerivedCounit L S =
      F.totalLeftDerivedCounit L S ≫ τ := by
  exact Functor.leftDerivedNatTrans_fac _ _ _ _ S τ

/-- Objectwise compatibility of the left-derived map with the total derived counits. -/
@[reassoc (attr := simp)]
theorem mapNatTrans.fac_app
    (L : C ⥤ D) (S : MorphismProperty C) {F G : C ⥤ E} (τ : F ⟶ G)
    [L.IsLocalization S] [F.HasLeftDerivedFunctor S] [G.HasLeftDerivedFunctor S] (X : C) :
    (mapNatTrans L S τ).app (L.obj X) ≫ (G.totalLeftDerivedCounit L S).app X =
      (F.totalLeftDerivedCounit L S).app X ≫ τ.app X := by
  exact Functor.leftDerivedNatTrans_app _ _ _ _ S τ X

/-- The total left-derived map induced by an identity transformation is the identity. -/
@[simp]
theorem mapNatTrans.id
    (L : C ⥤ D) (S : MorphismProperty C) (F : C ⥤ E)
    [L.IsLocalization S] [F.HasLeftDerivedFunctor S] :
    mapNatTrans L S (𝟙 F) = 𝟙 (F.totalLeftDerived L S) := by
  exact Functor.leftDerivedNatTrans_id _ _ S

/-- Total left-derived maps preserve composition of source natural transformations. -/
@[simp]
theorem mapNatTrans.comp
    (L : C ⥤ D) (S : MorphismProperty C) {F G K : C ⥤ E}
    (τ : F ⟶ G) (σ : G ⟶ K) [L.IsLocalization S]
    [F.HasLeftDerivedFunctor S] [G.HasLeftDerivedFunctor S]
    [K.HasLeftDerivedFunctor S] :
    mapNatTrans L S (τ ≫ σ) = mapNatTrans L S τ ≫ mapNatTrans L S σ := by
  exact (Functor.leftDerivedNatTrans_comp _ _ _ _ _ _ S τ σ).symm

/- An invertible natural transformation is enough to expose the corresponding derived
invertibility without forcing callers to manufacture an `Iso`. -/
/-- A total left-derived map induced by an invertible natural transformation is invertible. -/
theorem mapNatTrans_isIso
    (L : C ⥤ D) (S : MorphismProperty C) {F G : C ⥤ E} (τ : F ⟶ G)
    [L.IsLocalization S] [F.HasLeftDerivedFunctor S] [G.HasLeftDerivedFunctor S]
    [IsIso τ] :
    IsIso (mapNatTrans L S τ) := by
  change IsIso (Functor.leftDerivedNatIso
    (F.totalLeftDerived L S) (G.totalLeftDerived L S)
    (F.totalLeftDerivedCounit L S) (G.totalLeftDerivedCounit L S) S (asIso τ)).hom
  infer_instance

/-- The isomorphism between chosen total left-derived functors induced by a natural
isomorphism. -/
noncomputable def mapNatIso
    (L : C ⥤ D) (S : MorphismProperty C) {F G : C ⥤ E} (e : F ≅ G)
    [L.IsLocalization S] [F.HasLeftDerivedFunctor S] [G.HasLeftDerivedFunctor S] :
    F.totalLeftDerived L S ≅ G.totalLeftDerived L S :=
  Functor.leftDerivedNatIso
    (F.totalLeftDerived L S) (G.totalLeftDerived L S)
    (F.totalLeftDerivedCounit L S) (G.totalLeftDerivedCounit L S) S e

/-- The hom of the induced total left-derived isomorphism is `mapNatTrans` on the hom. -/
@[simp]
theorem mapNatIso.hom
    (L : C ⥤ D) (S : MorphismProperty C) {F G : C ⥤ E} (e : F ≅ G)
    [L.IsLocalization S] [F.HasLeftDerivedFunctor S] [G.HasLeftDerivedFunctor S] :
    (mapNatIso L S e).hom = mapNatTrans L S e.hom := by
  rfl

/-- The inverse of the induced total left-derived isomorphism is `mapNatTrans` on the inverse. -/
@[simp]
theorem mapNatIso.inv
    (L : C ⥤ D) (S : MorphismProperty C) {F G : C ⥤ E} (e : F ≅ G)
    [L.IsLocalization S] [F.HasLeftDerivedFunctor S] [G.HasLeftDerivedFunctor S] :
    (mapNatIso L S e).inv = mapNatTrans L S e.inv := by
  rfl

/-- Total left-derived natural isomorphisms preserve reflexivity. -/
@[simp]
theorem mapNatIso.refl
    (L : C ⥤ D) (S : MorphismProperty C) (F : C ⥤ E)
    [L.IsLocalization S] [F.HasLeftDerivedFunctor S] :
    mapNatIso L S (Iso.refl F) = Iso.refl (F.totalLeftDerived L S) := by
  apply Iso.ext
  exact mapNatTrans.id L S F

/-- Total left-derived natural isomorphisms preserve symmetry. -/
@[simp]
theorem mapNatIso.symm
    (L : C ⥤ D) (S : MorphismProperty C) {F G : C ⥤ E} (e : F ≅ G)
    [L.IsLocalization S] [F.HasLeftDerivedFunctor S] [G.HasLeftDerivedFunctor S] :
    mapNatIso L S e.symm = (mapNatIso L S e).symm := by
  apply Iso.ext
  rfl

/-- Total left-derived natural isomorphisms preserve transitivity. -/
@[simp]
theorem mapNatIso.trans
    (L : C ⥤ D) (S : MorphismProperty C) {F G K : C ⥤ E}
    (e : F ≅ G) (e' : G ≅ K) [L.IsLocalization S]
    [F.HasLeftDerivedFunctor S] [G.HasLeftDerivedFunctor S]
    [K.HasLeftDerivedFunctor S] :
    mapNatIso L S (e ≪≫ e') = mapNatIso L S e ≪≫ mapNatIso L S e' := by
  apply Iso.ext
  exact mapNatTrans.comp L S e.hom e'.hom

end CategoryTheory.Functor.LeftDerived
