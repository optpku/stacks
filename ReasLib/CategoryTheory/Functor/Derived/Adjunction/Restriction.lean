/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import ReasLib.CategoryTheory.Functor.Derived.Localization

/-!
# Derived Adjunctions with a Descended Right Adjoint

This file compares arbitrary left- and right-derived models with localization lifts.  It then
transports Mathlib's derived adjunction across such a comparison on the right.  The construction
is independent of differential graded algebras and can be reused for any pair of localization
functors.
-/

@[expose] public section

noncomputable section

universe uC uD uH vC vD vH
universe uC1 uC2 uD1 uD2 vC1 vC2 vD1 vD2

namespace CategoryTheory.Functor

namespace IsRightDerivedFunctor

variable {C : Type uC} {D : Type uD} {H : Type uH}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vH} H]
variable {F G : C ⥤ H} (W : MorphismProperty C)
variable {L : C ⥤ D} [L.IsLocalization W]

/-- A right-derived model of a functor naturally isomorphic to an inverted functor is canonically
isomorphic to the latter functor's localization lift. -/
@[stacks 0BYX "right-derived functor as a descended restriction functor"]
noncomputable def isoLiftOfIso (RF : D ⥤ H) (α : F ⟶ L ⋙ RF)
    [RF.IsRightDerivedFunctor α W] (hG : W.IsInvertedBy G) (e : F ≅ G) :
    RF ≅ Localization.lift G hG L :=
  Functor.rightDerivedNatIso RF (Localization.lift G hG L)
    α (Localization.fac G hG L).inv W e

end IsRightDerivedFunctor

namespace RightDerived

variable {C : Type uC} {D : Type uD} {H : Type uH}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vH} H]
variable {F G : C ⥤ H} (W : MorphismProperty C)
variable {L : C ⥤ D} [L.IsLocalization W]

/-- The total right-derived functor of a functor naturally isomorphic to an inverted functor is
canonically isomorphic to the latter functor's localization lift. -/
@[stacks 0BYX "total right-derived functor as a localization lift"]
noncomputable def totalIsoLiftOfIso [F.HasRightDerivedFunctor W]
    (hG : W.IsInvertedBy G) (e : F ≅ G) :
    F.totalRightDerived L W ≅ Localization.lift G hG L :=
  IsRightDerivedFunctor.isoLiftOfIso W (F.totalRightDerived L W)
    (F.totalRightDerivedUnit L W) hG e

end RightDerived

namespace IsLeftDerivedFunctor

variable {C : Type uC} {D : Type uD} {H : Type uH}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vH} H]
variable {F G : C ⥤ H} (W : MorphismProperty C)
variable {L : C ⥤ D} [L.IsLocalization W]

/-- The localization lift of an inverted functor is canonically isomorphic to any left-derived
model of a naturally isomorphic functor. -/
@[stacks 0BYX "descended restriction as a derived tensor functor"]
noncomputable def liftIsoOfIso (LF : D ⥤ H) (α : L ⋙ LF ⟶ G)
    [LF.IsLeftDerivedFunctor α W] (hF : W.IsInvertedBy F) (e : F ≅ G) :
    Localization.lift F hF L ≅ LF :=
  Functor.leftDerivedNatIso (Localization.lift F hF L) LF
    (Localization.fac F hF L).hom α W e

end IsLeftDerivedFunctor

namespace LeftDerived

variable {C : Type uC} {D : Type uD} {H : Type uH}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vH} H]
variable {F G : C ⥤ H} (W : MorphismProperty C)
variable {L : C ⥤ D} [L.IsLocalization W]

/-- The localization lift of an inverted functor is canonically isomorphic to the total
left-derived functor of a naturally isomorphic functor. -/
@[stacks 0BYX "localization lift as a total left-derived functor"]
noncomputable def liftIsoTotalOfIso [G.HasLeftDerivedFunctor W]
    (hF : W.IsInvertedBy F) (e : F ≅ G) :
    Localization.lift F hF L ≅ G.totalLeftDerived L W :=
  IsLeftDerivedFunctor.liftIsoOfIso W (G.totalLeftDerived L W)
    (G.totalLeftDerivedCounit L W) hF e

end LeftDerived

end CategoryTheory.Functor

namespace CategoryTheory.Adjunction.TotalDerived

variable {C1 : Type uC1} {C2 : Type uC2} {D1 : Type uD1} {D2 : Type uD2}
variable [Category.{vC1} C1] [Category.{vC2} C2]
variable [Category.{vD1} D1] [Category.{vD2} D2]
variable {G : C1 ⥤ C2} {F : C2 ⥤ C1} (adj : G ⊣ F)

/-- The canonical total left- and right-derived functors of an adjoint pair remain derived after
composition with one another. This is precisely the absolute-derived hypothesis required by
`Adjunction.derived`. -/
@[stacks 0BYX "absolute total-derived adjunction pair"]
class HasPair (W1 : MorphismProperty C1) (W2 : MorphismProperty C2)
    {L1 : C1 ⥤ D1} {L2 : C2 ⥤ D2}
    [L1.IsLocalization W1] [L2.IsLocalization W2]
    [(G ⋙ L2).HasLeftDerivedFunctor W1]
    [(F ⋙ L1).HasRightDerivedFunctor W2] : Prop extends
    ((G ⋙ L2).totalLeftDerived L1 W1 ⋙
      (F ⋙ L1).totalRightDerived L2 W2).IsLeftDerivedFunctor
        ((Functor.associator L1 ((G ⋙ L2).totalLeftDerived L1 W1)
            ((F ⋙ L1).totalRightDerived L2 W2)).inv ≫
          Functor.whiskerRight ((G ⋙ L2).totalLeftDerivedCounit L1 W1)
            ((F ⋙ L1).totalRightDerived L2 W2)) W1,
    ((F ⋙ L1).totalRightDerived L2 W2 ⋙
      (G ⋙ L2).totalLeftDerived L1 W1).IsRightDerivedFunctor
        (Functor.whiskerRight ((F ⋙ L1).totalRightDerivedUnit L2 W2)
            ((G ⋙ L2).totalLeftDerived L1 W1) ≫
          (Functor.associator L2 ((F ⋙ L1).totalRightDerived L2 W2)
            ((G ⋙ L2).totalLeftDerived L1 W1)).hom) W2

/-- The absolute total-derived pair condition consists exactly of the two composite-derived
conditions used by `Adjunction.derived`. -/
@[stacks 0BYX "absolute total-derived pair criterion"]
theorem hasPair_iff
    (W1 : MorphismProperty C1) (W2 : MorphismProperty C2)
    {L1 : C1 ⥤ D1} {L2 : C2 ⥤ D2}
    [L1.IsLocalization W1] [L2.IsLocalization W2]
    [(G ⋙ L2).HasLeftDerivedFunctor W1]
    [(F ⋙ L1).HasRightDerivedFunctor W2] :
    HasPair (G := G) (F := F) W1 W2 (L1 := L1) (L2 := L2) ↔
      (((G ⋙ L2).totalLeftDerived L1 W1 ⋙
          (F ⋙ L1).totalRightDerived L2 W2).IsLeftDerivedFunctor
        ((Functor.associator L1 ((G ⋙ L2).totalLeftDerived L1 W1)
              ((F ⋙ L1).totalRightDerived L2 W2)).inv ≫
          Functor.whiskerRight ((G ⋙ L2).totalLeftDerivedCounit L1 W1)
            ((F ⋙ L1).totalRightDerived L2 W2)) W1 ∧
        ((F ⋙ L1).totalRightDerived L2 W2 ⋙
          (G ⋙ L2).totalLeftDerived L1 W1).IsRightDerivedFunctor
        (Functor.whiskerRight ((F ⋙ L1).totalRightDerivedUnit L2 W2)
              ((G ⋙ L2).totalLeftDerived L1 W1) ≫
          (Functor.associator L2 ((F ⋙ L1).totalRightDerived L2 W2)
            ((G ⋙ L2).totalLeftDerived L1 W1)).hom) W2) := sorry

/-- Construct the derived adjunction from the bundled absolute-derived pair condition. -/
@[stacks 0BYX "adjunction from an absolute total-derived pair"]
noncomputable def HasPair.derived
    (W1 : MorphismProperty C1) (W2 : MorphismProperty C2)
    {L1 : C1 ⥤ D1} {L2 : C2 ⥤ D2}
    [L1.IsLocalization W1] [L2.IsLocalization W2]
    [(G ⋙ L2).HasLeftDerivedFunctor W1]
    [(F ⋙ L1).HasRightDerivedFunctor W2]
    [h : HasPair (G := G) (F := F) W1 W2 (L1 := L1) (L2 := L2)] :
    (G ⋙ L2).totalLeftDerived L1 W1 ⊣
      (F ⋙ L1).totalRightDerived L2 W2 :=
  adj.derived W1 W2
    ((G ⋙ L2).totalLeftDerivedCounit L1 W1)
    ((F ⋙ L1).totalRightDerivedUnit L2 W2)

/-- The total-derived adjunction is independent of the proof of the absolute-derived pair
condition. -/
@[stacks 0BYX "total-derived adjunction proof independence"]
theorem HasPair.derived_eq
    (W1 : MorphismProperty C1) (W2 : MorphismProperty C2)
    {L1 : C1 ⥤ D1} {L2 : C2 ⥤ D2}
    [L1.IsLocalization W1] [L2.IsLocalization W2]
    [(G ⋙ L2).HasLeftDerivedFunctor W1]
    [(F ⋙ L1).HasRightDerivedFunctor W2]
    (h₁ h₂ : HasPair (G := G) (F := F) W1 W2 (L1 := L1) (L2 := L2)) :
    HasPair.derived (G := G) (F := F) (h := h₁) adj W1 W2
      (L1 := L1) (L2 := L2) =
      HasPair.derived (G := G) (F := F) (h := h₂) adj W1 W2
        (L1 := L1) (L2 := L2) := sorry

/-- The unit of the total-derived adjunction satisfies the canonical factorization through the
underived unit and the two derived-functor structure maps. -/
@[stacks 0BYX "total-derived adjunction unit factorization"]
theorem HasPair.derived_unit_fac_app
    (W1 : MorphismProperty C1) (W2 : MorphismProperty C2)
    {L1 : C1 ⥤ D1} {L2 : C2 ⥤ D2}
    [L1.IsLocalization W1] [L2.IsLocalization W2]
    [(G ⋙ L2).HasLeftDerivedFunctor W1]
    [(F ⋙ L1).HasRightDerivedFunctor W2]
    [HasPair (G := G) (F := F) W1 W2 (L1 := L1) (L2 := L2)]
    (X : C1) :
    (HasPair.derived adj W1 W2).unit.app (L1.obj X) ≫
        ((F ⋙ L1).totalRightDerived L2 W2).map
          (((G ⋙ L2).totalLeftDerivedCounit L1 W1).app X) =
      L1.map (adj.unit.app X) ≫
        ((F ⋙ L1).totalRightDerivedUnit L2 W2).app (G.obj X) := sorry

/-- The counit of the total-derived adjunction satisfies the canonical factorization through the
underived counit and the two derived-functor structure maps. -/
@[stacks 0BYX "total-derived adjunction counit factorization",
  stacks 0FPI "derived pullback-pushforward counit square"]
theorem HasPair.derived_counit_fac_app
    (W1 : MorphismProperty C1) (W2 : MorphismProperty C2)
    {L1 : C1 ⥤ D1} {L2 : C2 ⥤ D2}
    [L1.IsLocalization W1] [L2.IsLocalization W2]
    [(G ⋙ L2).HasLeftDerivedFunctor W1]
    [(F ⋙ L1).HasRightDerivedFunctor W2]
    [HasPair (G := G) (F := F) W1 W2 (L1 := L1) (L2 := L2)]
    (X : C2) :
    ((G ⋙ L2).totalLeftDerived L1 W1).map
          (((F ⋙ L1).totalRightDerivedUnit L2 W2).app X) ≫
        (HasPair.derived adj W1 W2).counit.app (L2.obj X) =
      ((G ⋙ L2).totalLeftDerivedCounit L1 W1).app (F.obj X) ≫
        L2.map (adj.counit.app X) := sorry

/-- If the underived right adjoint is naturally isomorphic to a functor which descends through
the localization, then the canonical total left-derived functor is left adjoint to that descended
functor. -/
@[stacks 0BYX "derived tensor is left adjoint to descended restriction"]
noncomputable def withDescendedRight
    {S : C2 ⥤ C1}
    (W1 : MorphismProperty C1) (W2 : MorphismProperty C2)
    {L1 : C1 ⥤ D1} {L2 : C2 ⥤ D2}
    [L1.IsLocalization W1] [L2.IsLocalization W2]
    [(G ⋙ L2).HasLeftDerivedFunctor W1]
    [(F ⋙ L1).HasRightDerivedFunctor W2]
    [HasPair (G := G) (F := F) W1 W2 (L1 := L1) (L2 := L2)]
    (hS : W2.IsInvertedBy (S ⋙ L1)) (e : F ≅ S) :
    (G ⋙ L2).totalLeftDerived L1 W1 ⊣ Localization.lift (S ⋙ L1) hS L2 :=
  (HasPair.derived adj W1 W2).ofNatIsoRight
    (Functor.IsRightDerivedFunctor.isoLiftOfIso W2
      ((F ⋙ L1).totalRightDerived L2 W2)
      ((F ⋙ L1).totalRightDerivedUnit L2 W2) hS
      (Functor.isoWhiskerRight e L1))

/-- The hom-set equivalence induced by `withDescendedRight`. -/
@[stacks 0BYX "derived tensor-Hom equivalence with descended right adjoint"]
noncomputable def homEquivDescendedRight
    {S : C2 ⥤ C1}
    (W1 : MorphismProperty C1) (W2 : MorphismProperty C2)
    {L1 : C1 ⥤ D1} {L2 : C2 ⥤ D2}
    [L1.IsLocalization W1] [L2.IsLocalization W2]
    [(G ⋙ L2).HasLeftDerivedFunctor W1]
    [(F ⋙ L1).HasRightDerivedFunctor W2]
    [HasPair (G := G) (F := F) W1 W2 (L1 := L1) (L2 := L2)]
    (hS : W2.IsInvertedBy (S ⋙ L1)) (e : F ≅ S) (X : D1) (Y : D2) :
    (((G ⋙ L2).totalLeftDerived L1 W1).obj X ⟶ Y) ≃
      (X ⟶ (Localization.lift (S ⋙ L1) hS L2).obj Y) :=
  (withDescendedRight adj W1 W2 hS e).homEquiv X Y

end CategoryTheory.Adjunction.TotalDerived
