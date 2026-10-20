module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Below.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Canonical
public import ReasLib.CategoryTheory.Functor.Derived.Naturality.Right
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of canonical bounded-below right-derived functors

Natural transformations of additive functors induce natural transformations between their
canonical total right-derived functors on bounded-below derived categories.  This is the
bounded-below specialization of Mathlib's universal `Functor.rightDerivedNatTrans` construction.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.Functor.RightDerived.Bounded

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]

/-- A natural transformation of additive functors induces a natural transformation between
their canonical bounded-below total right-derived functors. -/
@[stacks 05T2 "naturality of bounded-below total right-derived functors"]
noncomputable def map
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [G.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (τ : F ⟶ G) : functor F ⟶ functor G :=
  RightDerived.mapNatTrans
    (DerivedCategory.Plus.Qh : HomotopyCategory.Plus A ⥤ DerivedCategory.Plus A)
    (HomotopyCategory.Plus.quasiIso A) (NatTrans.toBoundedBelowDerived τ)

/-- The induced map on bounded-below right-derived functors is characterized by the canonical
localization units. -/
@[reassoc (attr := simp), stacks 05T2 "bounded-below right-derived naturality factorization"]
theorem map_fac
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [G.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (τ : F ⟶ G) :
    unit F ≫ Functor.whiskerLeft DerivedCategory.Plus.Qh (map τ) =
      NatTrans.toBoundedBelowDerived τ ≫ unit G := sorry

/-- Componentwise form of the bounded-below right-derived naturality factorization. -/
@[reassoc (attr := simp), stacks 05T2 "bounded-below right-derived naturality component"]
theorem map_fac_app
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [G.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (τ : F ⟶ G) (K : HomotopyCategory.Plus A) :
    (unit F).app K ≫ (map τ).app (DerivedCategory.Plus.Qh.obj K) =
      (NatTrans.toBoundedBelowDerived τ).app K ≫ (unit G).app K := sorry

/-- The bounded-below right-derived action preserves identity transformations. -/
@[simp, stacks 05T2 "bounded-below right-derived identity"]
theorem map_id
    (F : A ⥤ B) [F.Additive]
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)] :
    map (𝟙 F) = 𝟙 (functor F) := sorry

/-- The bounded-below right-derived action preserves composition of natural transformations. -/
@[simp, stacks 05T2 "bounded-below right-derived composition"]
theorem map_comp
    {F G H : A ⥤ B} [F.Additive] [G.Additive] [H.Additive]
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [G.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [H.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (τ : F ⟶ G) (σ : G ⟶ H) :
    map (τ ≫ σ) = map τ ≫ map σ := sorry

/-- An invertible underived transformation remains invertible after bounded-below total
right derivation. -/
@[stacks 05T2 "bounded-below right-derived isomorphism preservation"]
theorem map_isIso
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [G.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (τ : F ⟶ G) [IsIso τ] :
    IsIso (map τ) := sorry

end CategoryTheory.Functor.RightDerived.Bounded
