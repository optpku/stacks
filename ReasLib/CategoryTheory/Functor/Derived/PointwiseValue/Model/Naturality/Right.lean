/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Model.Functor.Right
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Naturality.Functor.Right
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Naturality of Right-Derived Model Comparisons

A morphism between arbitrary right-derived models that commutes with their units induces the
same map on pointwise values as the underlying natural transformation.
-/

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]

namespace RightDerived.Value.modelNatIso

/-- Compatibility of a morphism of right-derived models with the induced map on pointwise
right-derived value functors. -/
@[reassoc (attr := simp), stacks 05SA]
theorem mapNatTrans
    (S : MorphismProperty C) {F G : C ⥤ D}
    {RF RG : S.Localization ⥤ D} {α : F ⟶ S.Q ⋙ RF} {β : G ⟶ S.Q ⋙ RG}
    [RF.IsRightDerivedFunctor α S] [RG.IsRightDerivedFunctor β S]
    [F.HasPointwiseRightDerivedFunctor S] [G.HasPointwiseRightDerivedFunctor S]
    (τ : F ⟶ G) (γ : RF ⟶ RG)
    (fac : α ≫ whiskerLeft S.Q γ = τ ≫ β) :
    whiskerLeft S.Q γ ≫ (RightDerived.Value.modelNatIso G S RG β).hom =
      (RightDerived.Value.modelNatIso F S RF α).hom ≫
        RightDerived.Value.mapNatTrans S τ := sorry

/-- Objectwise compatibility of a morphism of right-derived models with the induced pointwise
map. -/
@[reassoc (attr := simp), stacks 05SA]
theorem mapNatTrans_app
    (S : MorphismProperty C) {F G : C ⥤ D}
    {RF RG : S.Localization ⥤ D} {α : F ⟶ S.Q ⋙ RF} {β : G ⟶ S.Q ⋙ RG}
    [RF.IsRightDerivedFunctor α S] [RG.IsRightDerivedFunctor β S]
    [F.HasPointwiseRightDerivedFunctor S] [G.HasPointwiseRightDerivedFunctor S]
    (τ : F ⟶ G) (γ : RF ⟶ RG)
    (fac : α ≫ whiskerLeft S.Q γ = τ ≫ β) (X : C) :
    γ.app (S.Q.obj X) ≫ (RightDerived.Value.modelIso G S RG β X).hom =
      (RightDerived.Value.modelIso F S RF α X).hom ≫
        RightDerived.Value.mapNatTrans.component S τ X := sorry

/-- Inverse compatibility of a morphism of right-derived models with the induced pointwise map. -/
@[reassoc (attr := simp), stacks 05SA]
theorem mapNatTrans_inv
    (S : MorphismProperty C) {F G : C ⥤ D}
    {RF RG : S.Localization ⥤ D} {α : F ⟶ S.Q ⋙ RF} {β : G ⟶ S.Q ⋙ RG}
    [RF.IsRightDerivedFunctor α S] [RG.IsRightDerivedFunctor β S]
    [F.HasPointwiseRightDerivedFunctor S] [G.HasPointwiseRightDerivedFunctor S]
    (τ : F ⟶ G) (γ : RF ⟶ RG)
    (fac : α ≫ whiskerLeft S.Q γ = τ ≫ β) :
    RightDerived.Value.mapNatTrans S τ ≫
        (RightDerived.Value.modelNatIso G S RG β).inv =
      (RightDerived.Value.modelNatIso F S RF α).inv ≫ whiskerLeft S.Q γ := sorry

/-- Objectwise inverse compatibility of a morphism of right-derived models. -/
@[reassoc (attr := simp), stacks 05SA]
theorem mapNatTrans_inv_app
    (S : MorphismProperty C) {F G : C ⥤ D}
    {RF RG : S.Localization ⥤ D} {α : F ⟶ S.Q ⋙ RF} {β : G ⟶ S.Q ⋙ RG}
    [RF.IsRightDerivedFunctor α S] [RG.IsRightDerivedFunctor β S]
    [F.HasPointwiseRightDerivedFunctor S] [G.HasPointwiseRightDerivedFunctor S]
    (τ : F ⟶ G) (γ : RF ⟶ RG)
    (fac : α ≫ whiskerLeft S.Q γ = τ ≫ β) (X : C) :
    RightDerived.Value.mapNatTrans.component S τ X ≫
        (RightDerived.Value.modelIso G S RG β X).inv =
      (RightDerived.Value.modelIso F S RF α X).inv ≫ γ.app (S.Q.obj X) := sorry

/-- Iso-level compatibility of isomorphic right-derived models with pointwise values. -/
@[stacks 05SA]
theorem mapNatIso
    (S : MorphismProperty C) {F G : C ⥤ D}
    {RF RG : S.Localization ⥤ D} {α : F ⟶ S.Q ⋙ RF} {β : G ⟶ S.Q ⋙ RG}
    [RF.IsRightDerivedFunctor α S] [RG.IsRightDerivedFunctor β S]
    [F.HasPointwiseRightDerivedFunctor S] [G.HasPointwiseRightDerivedFunctor S]
    (e : F ≅ G) (ε : RF ≅ RG)
    (fac : α ≫ whiskerLeft S.Q ε.hom = e.hom ≫ β) :
    Functor.isoWhiskerLeft S.Q ε ≪≫ RightDerived.Value.modelNatIso G S RG β =
      RightDerived.Value.modelNatIso F S RF α ≪≫ RightDerived.Value.mapNatIso S e := sorry

end RightDerived.Value.modelNatIso

end CategoryTheory.Functor
