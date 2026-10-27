/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.FiberCartesian

/-!
# Quasi-coherent modules on a fiberwise simplicial site

A module on the total site is quasi-coherent exactly when it is cartesian and
its restriction to every fiber is quasi-coherent.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite

noncomputable section

universe u v w

namespace CategoryTheory.Grothendieck

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
variable [∀ U : Grothendieck F, ((topology F J).over U).HasSheafCompose
    (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ U : Grothendieck F, HasWeakSheafify ((topology F J).over U) AddCommGrpCat.{w}]
variable [∀ U : Grothendieck F, ((topology F J).over U).WEqualsLocallyBijective
    AddCommGrpCat.{w}]
variable [∀ (n : SimplexCategory) (U : F.obj (op n)),
    (((J (op n)).toGrothendieck).over U).HasSheafCompose
      (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ (n : SimplexCategory) (U : F.obj (op n)),
    HasWeakSheafify (((J (op n)).toGrothendieck).over U) AddCommGrpCat.{w}]
variable [∀ (n : SimplexCategory) (U : F.obj (op n)),
    (((J (op n)).toGrothendieck).over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- A module over a sheaf of rings on a fiberwise total simplicial site is quasi-coherent
if and only if it is cartesian and every fiber restriction is quasi-coherent. -/
@[stacks 0D7M]
theorem module_isQuasicoherent_iff
    (M : SheafOfModules.{w} (fiberTotalRingedSite F J O).structureSheaf) :
    M.IsQuasicoherent ↔
      Module.IsCartesian F J O M ∧
        ∀ n : SimplexCategory, ((moduleComponent F J O n).obj M).IsQuasicoherent :=
  sorry

/-- A quasi-coherent module on a fiberwise total simplicial site is cartesian. -/
instance instModuleIsCartesian_of_isQuasicoherent
    (M : SheafOfModules.{w} (fiberTotalRingedSite F J O).structureSheaf)
    [M.IsQuasicoherent] :
    Module.IsCartesian F J O M :=
  sorry

/-- Every fiber restriction of a quasi-coherent module on the total site is quasi-coherent. -/
instance instModuleComponent_isQuasicoherent
    (M : SheafOfModules.{w} (fiberTotalRingedSite F J O).structureSheaf)
    [M.IsQuasicoherent] (n : SimplexCategory) :
    ((moduleComponent F J O n).obj M).IsQuasicoherent :=
  sorry

/-- A cartesian module on a fiberwise total simplicial site with quasi-coherent fiber
restrictions is quasi-coherent. -/
instance instIsQuasicoherent_of_isCartesian
    (M : SheafOfModules.{w} (fiberTotalRingedSite F J O).structureSheaf)
    [Module.IsCartesian F J O M]
    [∀ n : SimplexCategory, ((moduleComponent F J O n).obj M).IsQuasicoherent] :
    M.IsQuasicoherent :=
  sorry

end CategoryTheory.Grothendieck
