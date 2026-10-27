/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.FiberCartesian
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Flat

/-!
# Closure of cartesian modules on a fiberwise simplicial ringed site
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty Opposite RingedSite

universe u v w u' v'

namespace CategoryTheory.Grothendieck.Module

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable (O : Sheaf (topology F J) RingCat.{w})
variable [UnivLE.{max u v, w}]
variable [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (fiberRingedToposMap F J O φ).structureMap).IsRightAdjoint]

/-- Cartesian modules over a ring sheaf on a fiberwise simplicial total site
form a weak Serre subcategory if every coface morphism of ringed topoi is flat. -/
theorem cartesianProperty_isWeakSerreClass
    [HasSheafify (topology F J) AddCommGrpCat.{w}]
    [(topology F J).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ {n : ℕ} (j : Fin (n + 2)),
      ToposHom.IsFlat (fiberRingedToposMap F J O (SimplexCategory.δ j))] :
    IsWeakSerreClass
      (fun M : SheafOfModules.{w} (fiberTotalRingedSite F J O).structureSheaf ↦
        IsCartesian F J O M) :=
  sorry

/-- A colimit of cartesian modules over a ring sheaf on a fiberwise simplicial
total site is cartesian whenever that colimit exists. -/
instance cartesianProperty_isClosedUnderColimitsOfShape
    (ι : Type u') [Category.{v'} ι] :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (fun M : SheafOfModules.{w} (fiberTotalRingedSite F J O).structureSheaf ↦
        IsCartesian F J O M) ι :=
  sorry

end CategoryTheory.Grothendieck.Module
