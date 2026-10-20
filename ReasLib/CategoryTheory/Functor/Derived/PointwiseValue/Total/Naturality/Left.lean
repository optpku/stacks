module

public import ReasLib.CategoryTheory.Functor.Derived.Naturality.Left
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Model.Naturality.Left
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Total.Functor.Left
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Naturality of the Total-to-Pointwise Left-Derived Comparison

The canonical comparison from a total left-derived functor to its pointwise value functor is
natural in the input functor, for both natural transformations and natural isomorphisms.
-/

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]

namespace LeftDerived.Value.totalNatIso

/-- The total-to-pointwise comparison intertwines the universal left-derived transformation
with the pointwise transformation induced by the same natural transformation. -/
@[stacks 05SA, reassoc (attr := simp)]
theorem mapNatTrans
    (S : MorphismProperty C) {F G : C ⥤ D} (τ : F ⟶ G)
    [F.HasPointwiseLeftDerivedFunctor S] [G.HasPointwiseLeftDerivedFunctor S] :
    whiskerLeft S.Q (LeftDerived.mapNatTrans S.Q S τ) ≫
        (LeftDerived.Value.totalNatIso G S).hom =
      (LeftDerived.Value.totalNatIso F S).hom ≫
        LeftDerived.Value.mapNatTrans S τ := sorry

/-- Objectwise form of compatibility between the total and pointwise left-derived
transformations. -/
@[stacks 05SA, reassoc (attr := simp)]
theorem mapNatTrans_app
    (S : MorphismProperty C) {F G : C ⥤ D} (τ : F ⟶ G)
    [F.HasPointwiseLeftDerivedFunctor S] [G.HasPointwiseLeftDerivedFunctor S] (X : C) :
    (LeftDerived.mapNatTrans S.Q S τ).app (S.Q.obj X) ≫
        (LeftDerived.Value.totalIso G S X).hom =
      (LeftDerived.Value.totalIso F S X).hom ≫
        LeftDerived.Value.mapNatTrans.component S τ X := sorry

/-- Inverse form of compatibility between the total and pointwise left-derived
transformations. -/
@[stacks 05SA, reassoc (attr := simp)]
theorem mapNatTrans_inv
    (S : MorphismProperty C) {F G : C ⥤ D} (τ : F ⟶ G)
    [F.HasPointwiseLeftDerivedFunctor S] [G.HasPointwiseLeftDerivedFunctor S] :
    LeftDerived.Value.mapNatTrans S τ ≫
        (LeftDerived.Value.totalNatIso G S).inv =
      (LeftDerived.Value.totalNatIso F S).inv ≫
        whiskerLeft S.Q (LeftDerived.mapNatTrans S.Q S τ) := sorry

/-- Objectwise inverse form of compatibility between the total and pointwise left-derived
transformations. -/
@[stacks 05SA, reassoc (attr := simp)]
theorem mapNatTrans_inv_app
    (S : MorphismProperty C) {F G : C ⥤ D} (τ : F ⟶ G)
    [F.HasPointwiseLeftDerivedFunctor S] [G.HasPointwiseLeftDerivedFunctor S] (X : C) :
    LeftDerived.Value.mapNatTrans.component S τ X ≫
        (LeftDerived.Value.totalIso G S X).inv =
      (LeftDerived.Value.totalIso F S X).inv ≫
        (LeftDerived.mapNatTrans S.Q S τ).app (S.Q.obj X) := sorry

/-- Iso-level naturality of the total-to-pointwise left-derived comparison. -/
@[stacks 05SA]
theorem mapNatIso
    (S : MorphismProperty C) {F G : C ⥤ D} (e : F ≅ G)
    [F.HasPointwiseLeftDerivedFunctor S] [G.HasPointwiseLeftDerivedFunctor S] :
    Functor.isoWhiskerLeft S.Q (LeftDerived.mapNatIso S.Q S e) ≪≫
        LeftDerived.Value.totalNatIso G S =
      LeftDerived.Value.totalNatIso F S ≪≫
        LeftDerived.Value.mapNatIso S e := sorry

end LeftDerived.Value.totalNatIso

end CategoryTheory.Functor
