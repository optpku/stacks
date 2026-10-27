/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.FiberCartesian
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Flat

@[expose] public section

open CategoryTheory
open scoped Simplicial
open RingedSite
open Opposite

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

variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (fiberRingedToposMap F J O φ).structureMap).IsRightAdjoint]
variable [∀ n, ToposHom.HasModulePullbackDerived (fiberStageMorphism F J O n)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (fiberRingedToposMap F J O φ)]

namespace ModuleDerived

/-- A morphism from a cartesian derived module object is zero if its degree-zero
component is zero, all simplex-operator structure maps are flat, and the component
Hom groups vanish in shifts `n` for `n > 0` and `n + 1` for `n ≥ 0`. -/
theorem hom_eq_zero
    (K K' : Hom.ModuleDerived.{w} (fiberTotalRingedSite F J O))
    [ModuleDerived.IsCartesian F J O K]
    (h_flat : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      ToposHom.IsFlat (fiberRingedToposMap F J O φ))
    (h_hom : ∀ n : SimplexCategory, 0 < n.len →
      Subsingleton (((moduleDerivedComponent F J O n).obj K)⟦(n.len : ℤ)⟧ ⟶
        (moduleDerivedComponent F J O n).obj K'))
    (h_hom_succ : ∀ n : SimplexCategory,
      Subsingleton (((moduleDerivedComponent F J O n).obj K)⟦(n.len + 1 : ℤ)⟧ ⟶
        (moduleDerivedComponent F J O n).obj K'))
    (f : K ⟶ K') (hf0 : (moduleDerivedComponent F J O ⦋0⦌).map f = 0) :
    f = 0 := sorry

end ModuleDerived

end CategoryTheory.Grothendieck
