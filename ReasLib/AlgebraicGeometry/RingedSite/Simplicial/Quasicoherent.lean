/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.Cartesian

/-!
# Quasi-coherent modules on a simplicial site

An `O`-module on the total site is quasi-coherent if and only if
it is cartesian and every stage restriction `F_n` is a quasi-coherent `O_n`-module.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open RingedSite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (f : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map f).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram.{u, v, w} C J]
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (f : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (ringedToposMap C J O f).structureMap).IsRightAdjoint]
variable [∀ U : totalSite C, ((topology C J).over U).HasSheafCompose
    (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ U : totalSite C, HasWeakSheafify ((topology C J).over U) AddCommGrpCat.{w}]
variable [∀ U : totalSite C, ((topology C J).over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ (n : SimplexCategory) (U : C.obj n),
    (((J n).toGrothendieck).over U).HasSheafCompose
      (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ (n : SimplexCategory) (U : C.obj n),
    HasWeakSheafify (((J n).toGrothendieck).over U) AddCommGrpCat.{w}]
variable [∀ (n : SimplexCategory) (U : C.obj n),
    (((J n).toGrothendieck).over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- A module over a sheaf of rings on a total simplicial site is quasi-coherent if and
only if it is cartesian and every stage restriction is quasi-coherent. -/
@[stacks 0D7M]
theorem module_isQuasicoherent_iff
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf) :
    F.IsQuasicoherent ↔
      Module.IsCartesian C J O F ∧
        ∀ n : SimplexCategory, ((moduleComponent C J O n).obj F).IsQuasicoherent :=
  sorry

/-- A quasi-coherent `O`-module on `C_total` is cartesian. -/
instance instModuleIsCartesian_of_isQuasicoherent
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf)
    [F.IsQuasicoherent] :
    Module.IsCartesian C J O F :=
  sorry

/-- The degree-`n` restriction of a quasi-coherent `O`-module on `C_total` is a
quasi-coherent `O_n`-module. -/
instance instModuleComponent_isQuasicoherent
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf)
    [F.IsQuasicoherent] (n : SimplexCategory) :
    ((moduleComponent C J O n).obj F).IsQuasicoherent :=
  sorry

/-- A cartesian `O`-module whose every stage restriction is quasi-coherent is
quasi-coherent on `C_total`. -/
instance instIsQuasicoherent_of_isCartesian
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf)
    [Module.IsCartesian C J O F]
    [∀ n : SimplexCategory, ((moduleComponent C J O n).obj F).IsQuasicoherent] :
    F.IsQuasicoherent :=
  sorry

end CategoryTheory.SimplicialSites
