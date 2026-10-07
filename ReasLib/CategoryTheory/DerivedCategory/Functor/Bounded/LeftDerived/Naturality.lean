module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Above.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.LeftDerived.Canonical
public import ReasLib.CategoryTheory.Functor.Derived.Naturality.Left
import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of canonical bounded-above left-derived functors

Natural transformations of additive functors induce natural transformations between their
canonical total left-derived functors on bounded-above derived categories.  This is the
bounded-above specialization of Mathlib's universal `Functor.leftDerivedNatTrans` construction.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w vA vB uA uB

namespace CategoryTheory.Functor.LeftDerived.Bounded

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]

/-- A natural transformation of additive functors induces a natural transformation between
their canonical bounded-above total left-derived functors. -/
@[stacks 05T2 "naturality of bounded-above total left-derived functors"]
noncomputable def map
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [F.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    [G.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    (τ : F ⟶ G) : functor F ⟶ functor G :=
  LeftDerived.mapNatTrans (DerivedCategory.Minus.Qh A)
    (HomotopyCategory.Minus.quasiIso A) (NatTrans.toBoundedAboveDerived τ)

/-- The induced map on bounded-above left-derived functors is characterized by the canonical
localization counits. -/
@[reassoc (attr := simp), stacks 05T2 "bounded-above left-derived naturality factorization"]
theorem map_fac
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [F.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    [G.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    (τ : F ⟶ G) :
    Functor.whiskerLeft (DerivedCategory.Minus.Qh A) (map τ) ≫ counit G =
      counit F ≫ NatTrans.toBoundedAboveDerived τ := sorry

/-- Componentwise form of the bounded-above left-derived naturality factorization. -/
@[reassoc (attr := simp), stacks 05T2 "bounded-above left-derived naturality component"]
theorem map_fac_app
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [F.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    [G.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    (τ : F ⟶ G) (K : HomotopyCategory.Minus A) :
    (map τ).app ((DerivedCategory.Minus.Qh A).obj K) ≫ (counit G).app K =
      (counit F).app K ≫ (NatTrans.toBoundedAboveDerived τ).app K := sorry

/-- The bounded-above left-derived action preserves identity transformations. -/
@[simp, stacks 05T2 "bounded-above left-derived identity"]
theorem map_id
    (F : A ⥤ B) [F.Additive]
    [F.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)] :
    map (𝟙 F) = 𝟙 (functor F) := sorry

/-- The bounded-above left-derived action preserves composition of natural transformations. -/
@[simp, stacks 05T2 "bounded-above left-derived composition"]
theorem map_comp
    {F G H : A ⥤ B} [F.Additive] [G.Additive] [H.Additive]
    [F.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    [G.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    [H.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    (τ : F ⟶ G) (σ : G ⟶ H) :
    map (τ ≫ σ) = map τ ≫ map σ := sorry

end CategoryTheory.Functor.LeftDerived.Bounded
