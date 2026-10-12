/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived.Composition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Total left derivation after an exact functor

If `F : A ⥤ₑ B` is exact and `G : B ⥤ C` admits a total left derived functor, then
`F.mapDerivedCategory ⋙ L G` has a canonical counit over `F.obj ⋙ G`.  An underived
transformation from this composite to an exact functor therefore descends, by fullness of the
localization, to a canonical transformation on derived categories.

The construction does not assert that the iterated functor is the total left derived functor of
the composite.  That stronger assertion is a separate composition-compatibility property.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe uA vA wA uB vB wB uC vC wC

namespace CategoryTheory.Functor.LeftDerived.Homotopy.Composition.ExactFirst

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]

/-- The canonical counit for an exact functor followed by a total left-derived functor. -/
@[stacks 05T2 "exact-first total-left-derived counit"]
noncomputable def counit (F : A ⥤ₑ B) (G : B ⥤ C) [G.Additive]
    [(Functor.Homotopy.toDerived G).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso B (up ℤ))] :
    (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A) ⋙
        (F.mapDerivedCategory ⋙ Functor.LeftDerived.Homotopy.functor G) ⟶
      Functor.Homotopy.toDerived (F.obj ⋙ G) :=
  (Functor.associator
      (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A)
      F.mapDerivedCategory (Functor.LeftDerived.Homotopy.functor G)).inv ≫
    Functor.whiskerRight F.obj.mapDerivedCategoryFactorsh.hom
      (Functor.LeftDerived.Homotopy.functor G) ≫
    (Functor.associator (F.obj.mapHomotopyCategory (up ℤ))
      (DerivedCategory.Qh : HomotopyCategory B (up ℤ) ⥤ DerivedCategory B)
      (Functor.LeftDerived.Homotopy.functor G)).hom ≫
    Functor.whiskerLeft (F.obj.mapHomotopyCategory (up ℤ))
      (Functor.LeftDerived.Homotopy.counit G) ≫
    (Functor.LeftDerived.Homotopy.Composition.toDerivedIso
      G F.obj (F.obj ⋙ G) (Iso.refl _)).inv

/-- The homotopy-level comparison induced by `τ : F.obj ⋙ G ⟶ H.obj`, where the target
functor `H` is exact. -/
@[stacks 05T2 "exact-first homotopy comparison"]
noncomputable def comparisonOnHomotopy
    (F : A ⥤ₑ B) (G : B ⥤ C) (H : A ⥤ₑ C) [G.Additive]
    [(Functor.Homotopy.toDerived G).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso B (up ℤ))]
    (τ : F.obj ⋙ G ⟶ H.obj) :
    (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A) ⋙
        (F.mapDerivedCategory ⋙ Functor.LeftDerived.Homotopy.functor G) ⟶
      (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A) ⋙
        H.mapDerivedCategory :=
  counit F G ≫
    Functor.whiskerRight (NatTrans.mapHomotopyCategory τ (up ℤ))
      (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C) ≫
    H.obj.mapDerivedCategoryFactorsh.inv

/-- The canonical derived comparison from an exact functor followed by a total left-derived
functor to an exact target. -/
@[stacks 05T2 "exact-first total-left-derived comparison"]
noncomputable def comparison
    (F : A ⥤ₑ B) (G : B ⥤ C) (H : A ⥤ₑ C) [G.Additive]
    [(Functor.Homotopy.toDerived G).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso B (up ℤ))]
    (τ : F.obj ⋙ G ⟶ H.obj) :
    F.mapDerivedCategory ⋙ Functor.LeftDerived.Homotopy.functor G ⟶
      H.mapDerivedCategory :=
  Localization.liftNatTrans
    (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A)
    (HomotopyCategory.quasiIso A (up ℤ))
    ((DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A) ⋙
      (F.mapDerivedCategory ⋙ Functor.LeftDerived.Homotopy.functor G))
    ((DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A) ⋙
      H.mapDerivedCategory)
    (F.mapDerivedCategory ⋙ Functor.LeftDerived.Homotopy.functor G)
    H.mapDerivedCategory (comparisonOnHomotopy F G H τ)

/-- Precomposing `comparison` with the localization recovers its explicit homotopy-level
comparison. -/
@[stacks 05T2 "exact-first comparison localization equation"]
theorem comparison_fac
    (F : A ⥤ₑ B) (G : B ⥤ C) (H : A ⥤ₑ C) [G.Additive]
    [(Functor.Homotopy.toDerived G).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso B (up ℤ))]
    (τ : F.obj ⋙ G ⟶ H.obj) :
    Functor.whiskerLeft
        (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A)
        (comparison F G H τ) =
      comparisonOnHomotopy F G H τ := by
  ext K
  simp [comparison]

end CategoryTheory.Functor.LeftDerived.Homotopy.Composition.ExactFirst
