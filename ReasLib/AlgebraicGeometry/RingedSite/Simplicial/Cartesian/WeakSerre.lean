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
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.Cartesian
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Flat

/-!
# Closure of cartesian modules on a simplicial ringed site
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty RingedSite

universe u v w u' v'

namespace CategoryTheory.SimplicialSites.Module

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (ringedToposMap C J O φ).structureMap).IsRightAdjoint]

/-- Cartesian modules over a ring sheaf on a simplicial total site form a weak
Serre subcategory if every coface morphism of ringed topoi is flat. -/
theorem cartesianProperty_isWeakSerreClass
    [HasSheafify (topology C J) AddCommGrpCat.{w}]
    [(topology C J).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ {n : ℕ} (j : Fin (n + 2)),
      ToposHom.IsFlat (ringedToposMap C J O (SimplexCategory.δ j))] :
    IsWeakSerreClass
      (fun M : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf ↦
        IsCartesian C J O M) :=
  sorry

/-- A colimit of cartesian modules over a ring sheaf on a simplicial total site
is cartesian whenever that colimit exists. -/
instance cartesianProperty_isClosedUnderColimitsOfShape
    (ι : Type u') [Category.{v'} ι] :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (fun M : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf ↦
        IsCartesian C J O M) ι :=
  sorry

end CategoryTheory.SimplicialSites.Module
