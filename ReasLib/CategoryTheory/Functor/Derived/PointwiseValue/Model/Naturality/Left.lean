module

public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Model.Functor.Left
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Naturality.Functor.Left
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Naturality of Left-Derived Model Comparisons

A morphism between arbitrary left-derived models that commutes with their counits induces the
same map on pointwise values as the underlying natural transformation.
-/

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]

namespace LeftDerived.Value.modelNatIso

/-- Compatibility of a morphism of left-derived models with the induced map on pointwise
left-derived value functors. -/
@[reassoc (attr := simp), stacks 05SA]
theorem mapNatTrans
    (S : MorphismProperty C) {F G : C ⥤ D}
    {LF LG : S.Localization ⥤ D} {α : S.Q ⋙ LF ⟶ F} {β : S.Q ⋙ LG ⟶ G}
    [LF.IsLeftDerivedFunctor α S] [LG.IsLeftDerivedFunctor β S]
    [F.HasPointwiseLeftDerivedFunctor S] [G.HasPointwiseLeftDerivedFunctor S]
    (τ : F ⟶ G) (γ : LF ⟶ LG)
    (fac : whiskerLeft S.Q γ ≫ β = α ≫ τ) :
    whiskerLeft S.Q γ ≫ (LeftDerived.Value.modelNatIso G S LG β).hom =
      (LeftDerived.Value.modelNatIso F S LF α).hom ≫
        LeftDerived.Value.mapNatTrans S τ := sorry

/-- Objectwise compatibility of a morphism of left-derived models with the induced pointwise
map. -/
@[reassoc (attr := simp), stacks 05SA]
theorem mapNatTrans_app
    (S : MorphismProperty C) {F G : C ⥤ D}
    {LF LG : S.Localization ⥤ D} {α : S.Q ⋙ LF ⟶ F} {β : S.Q ⋙ LG ⟶ G}
    [LF.IsLeftDerivedFunctor α S] [LG.IsLeftDerivedFunctor β S]
    [F.HasPointwiseLeftDerivedFunctor S] [G.HasPointwiseLeftDerivedFunctor S]
    (τ : F ⟶ G) (γ : LF ⟶ LG)
    (fac : whiskerLeft S.Q γ ≫ β = α ≫ τ) (X : C) :
    γ.app (S.Q.obj X) ≫ (LeftDerived.Value.modelIso G S LG β X).hom =
      (LeftDerived.Value.modelIso F S LF α X).hom ≫
        LeftDerived.Value.mapNatTrans.component S τ X := sorry

/-- Inverse compatibility of a morphism of left-derived models with the induced pointwise map. -/
@[reassoc (attr := simp), stacks 05SA]
theorem mapNatTrans_inv
    (S : MorphismProperty C) {F G : C ⥤ D}
    {LF LG : S.Localization ⥤ D} {α : S.Q ⋙ LF ⟶ F} {β : S.Q ⋙ LG ⟶ G}
    [LF.IsLeftDerivedFunctor α S] [LG.IsLeftDerivedFunctor β S]
    [F.HasPointwiseLeftDerivedFunctor S] [G.HasPointwiseLeftDerivedFunctor S]
    (τ : F ⟶ G) (γ : LF ⟶ LG)
    (fac : whiskerLeft S.Q γ ≫ β = α ≫ τ) :
    LeftDerived.Value.mapNatTrans S τ ≫
        (LeftDerived.Value.modelNatIso G S LG β).inv =
      (LeftDerived.Value.modelNatIso F S LF α).inv ≫ whiskerLeft S.Q γ := sorry

/-- Objectwise inverse compatibility of a morphism of left-derived models. -/
@[reassoc (attr := simp), stacks 05SA]
theorem mapNatTrans_inv_app
    (S : MorphismProperty C) {F G : C ⥤ D}
    {LF LG : S.Localization ⥤ D} {α : S.Q ⋙ LF ⟶ F} {β : S.Q ⋙ LG ⟶ G}
    [LF.IsLeftDerivedFunctor α S] [LG.IsLeftDerivedFunctor β S]
    [F.HasPointwiseLeftDerivedFunctor S] [G.HasPointwiseLeftDerivedFunctor S]
    (τ : F ⟶ G) (γ : LF ⟶ LG)
    (fac : whiskerLeft S.Q γ ≫ β = α ≫ τ) (X : C) :
    LeftDerived.Value.mapNatTrans.component S τ X ≫
        (LeftDerived.Value.modelIso G S LG β X).inv =
      (LeftDerived.Value.modelIso F S LF α X).inv ≫ γ.app (S.Q.obj X) := sorry

/-- Iso-level compatibility of isomorphic left-derived models with pointwise values. -/
@[stacks 05SA]
theorem mapNatIso
    (S : MorphismProperty C) {F G : C ⥤ D}
    {LF LG : S.Localization ⥤ D} {α : S.Q ⋙ LF ⟶ F} {β : S.Q ⋙ LG ⟶ G}
    [LF.IsLeftDerivedFunctor α S] [LG.IsLeftDerivedFunctor β S]
    [F.HasPointwiseLeftDerivedFunctor S] [G.HasPointwiseLeftDerivedFunctor S]
    (e : F ≅ G) (ε : LF ≅ LG)
    (fac : whiskerLeft S.Q ε.hom ≫ β = α ≫ e.hom) :
    Functor.isoWhiskerLeft S.Q ε ≪≫ LeftDerived.Value.modelNatIso G S LG β =
      LeftDerived.Value.modelNatIso F S LF α ≪≫ LeftDerived.Value.mapNatIso S e := sorry

end LeftDerived.Value.modelNatIso

end CategoryTheory.Functor
