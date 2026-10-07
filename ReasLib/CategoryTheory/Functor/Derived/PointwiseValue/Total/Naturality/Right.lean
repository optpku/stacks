module

public import ReasLib.CategoryTheory.Functor.Derived.Naturality.Right
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Model.Naturality.Right
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Total.Functor.Right
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Naturality of the Total-to-Pointwise Right-Derived Comparison

The canonical comparison from a total right-derived functor to its pointwise value functor is
natural in the input functor, for both natural transformations and natural isomorphisms.
-/

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]

namespace RightDerived.Value.totalNatIso

/-- The total-to-pointwise comparison intertwines the universal right-derived transformation
with the pointwise transformation induced by the same natural transformation. -/
@[stacks 05SA, reassoc (attr := simp)]
theorem mapNatTrans
    (S : MorphismProperty C) {F G : C ⥤ D} (τ : F ⟶ G)
    [F.HasPointwiseRightDerivedFunctor S] [G.HasPointwiseRightDerivedFunctor S] :
    whiskerLeft S.Q (RightDerived.mapNatTrans S.Q S τ) ≫
        (RightDerived.Value.totalNatIso G S).hom =
      (RightDerived.Value.totalNatIso F S).hom ≫
        RightDerived.Value.mapNatTrans S τ := sorry

/-- Objectwise form of compatibility between the total and pointwise right-derived
transformations. -/
@[stacks 05SA, reassoc (attr := simp)]
theorem mapNatTrans_app
    (S : MorphismProperty C) {F G : C ⥤ D} (τ : F ⟶ G)
    [F.HasPointwiseRightDerivedFunctor S] [G.HasPointwiseRightDerivedFunctor S] (X : C) :
    (RightDerived.mapNatTrans S.Q S τ).app (S.Q.obj X) ≫
        (RightDerived.Value.totalIso G S X).hom =
      (RightDerived.Value.totalIso F S X).hom ≫
        RightDerived.Value.mapNatTrans.component S τ X := sorry

/-- Inverse form of compatibility between the total and pointwise right-derived
transformations. -/
@[stacks 05SA, reassoc (attr := simp)]
theorem mapNatTrans_inv
    (S : MorphismProperty C) {F G : C ⥤ D} (τ : F ⟶ G)
    [F.HasPointwiseRightDerivedFunctor S] [G.HasPointwiseRightDerivedFunctor S] :
    RightDerived.Value.mapNatTrans S τ ≫
        (RightDerived.Value.totalNatIso G S).inv =
      (RightDerived.Value.totalNatIso F S).inv ≫
        whiskerLeft S.Q (RightDerived.mapNatTrans S.Q S τ) := sorry

/-- Objectwise inverse form of compatibility between the total and pointwise right-derived
transformations. -/
@[stacks 05SA, reassoc (attr := simp)]
theorem mapNatTrans_inv_app
    (S : MorphismProperty C) {F G : C ⥤ D} (τ : F ⟶ G)
    [F.HasPointwiseRightDerivedFunctor S] [G.HasPointwiseRightDerivedFunctor S] (X : C) :
    RightDerived.Value.mapNatTrans.component S τ X ≫
        (RightDerived.Value.totalIso G S X).inv =
      (RightDerived.Value.totalIso F S X).inv ≫
        (RightDerived.mapNatTrans S.Q S τ).app (S.Q.obj X) := sorry

/-- Iso-level naturality of the total-to-pointwise right-derived comparison. -/
@[stacks 05SA]
theorem mapNatIso
    (S : MorphismProperty C) {F G : C ⥤ D} (e : F ≅ G)
    [F.HasPointwiseRightDerivedFunctor S] [G.HasPointwiseRightDerivedFunctor S] :
    Functor.isoWhiskerLeft S.Q (RightDerived.mapNatIso S.Q S e) ≪≫
        RightDerived.Value.totalNatIso G S =
      RightDerived.Value.totalNatIso F S ≪≫
        RightDerived.Value.mapNatIso S e := sorry

end RightDerived.Value.totalNatIso

end CategoryTheory.Functor
