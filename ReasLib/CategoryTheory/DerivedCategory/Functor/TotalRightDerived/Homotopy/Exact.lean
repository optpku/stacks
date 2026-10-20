module

public import ReasLib.CategoryTheory.Functor.Derived.Exact
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Naturality
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exact functors and homotopy total right-derived functors

An exact additive functor has two standard presentations on derived categories: the direct
localization image and the homotopy total right-derived functor.  This leaf owns their canonical
comparison so downstream specializations do not rebuild localization witnesses.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe uA uB vA vB w

namespace CategoryTheory.Functor.RightDerived.Exact

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {B : Type uB} [Category.{vB} B] [Abelian B]
variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]

/-- The direct exact-derived presentation is canonically the homotopy total right-derived
presentation. -/
@[stacks 015F "exact and homotopy derived presentations"]
noncomputable def homotopyIso (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    F.mapDerivedCategory ≅ Functor.RightDerived.Homotopy.functor F :=
  Functor.RightDerived.natIsoOfIso
    (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A)
    (HomotopyCategory.quasiIso A (up ℤ))
    F.mapDerivedCategoryFactorsh.inv
    (Functor.RightDerived.Homotopy.unit F)
    (Iso.refl (Functor.Homotopy.toDerived F))

/-- The forward map of `homotopyIso` satisfies the right-derived universal-property equation. -/
@[simp, reassoc (attr := simp), stacks 015F "exact homotopy comparison forward equation"]
theorem homotopyIso_fac (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    F.mapDerivedCategoryFactorsh.inv ≫
        Functor.whiskerLeft
          (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A) (homotopyIso F).hom =
      Functor.RightDerived.Homotopy.unit F := sorry

/-- The inverse map of `homotopyIso` transports the homotopy unit back to the exact presentation. -/
@[simp, reassoc (attr := simp), stacks 015F "exact homotopy comparison inverse equation"]
theorem homotopyIso_inv_fac (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    Functor.RightDerived.Homotopy.unit F ≫
        Functor.whiskerLeft
          (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A) (homotopyIso F).inv =
      F.mapDerivedCategoryFactorsh.inv := sorry

end CategoryTheory.Functor.RightDerived.Exact
