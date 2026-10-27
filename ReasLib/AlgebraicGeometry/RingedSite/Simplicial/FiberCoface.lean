/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.FiberCartesian
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# Coface criteria for cartesian modules on fiberwise simplicial ringed sites
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite RingedSite

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

/-- A module sheaf on a fiberwise simplicial total ringed site is cartesian if and only if every
coface comparison is an isomorphism. -/
theorem Module.isCartesian_iff_delta
    (M : SheafOfModules.{w} (fiberTotalRingedSite F J O).structureSheaf) :
    Grothendieck.Module.IsCartesian F J O M ↔
      ∀ {n : ℕ} (j : Fin (n + 2)),
        IsIso (Grothendieck.moduleTransition F J O (SimplexCategory.δ j) M) := sorry

/-- An unbounded derived module on a fiberwise simplicial total ringed site is cartesian if and
only if every derived coface comparison is an isomorphism. -/
theorem ModuleDerived.isCartesian_iff_delta
    (K : Hom.ModuleDerived.{w} (fiberTotalRingedSite F J O)) :
    Grothendieck.ModuleDerived.IsCartesian F J O K ↔
      ∀ {n : ℕ} (j : Fin (n + 2)),
        IsIso (Grothendieck.moduleDerivedTransition F J O (SimplexCategory.δ j) K) := sorry

end CategoryTheory.Grothendieck
