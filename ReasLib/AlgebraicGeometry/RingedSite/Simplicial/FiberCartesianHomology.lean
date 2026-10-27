/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.FiberCartesian
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Flat

/-!
# Cohomology criterion for cartesian derived modules on a fiberwise site
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
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (fiberRingedToposMap F J O φ).structureMap).IsRightAdjoint]
variable [∀ n, ToposHom.HasModulePullbackDerived (fiberStageMorphism F J O n)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (fiberRingedToposMap F J O φ)]

/-- If every coface morphism of a fiberwise simplicial ringed site is flat, a derived
module is cartesian if and only if its cohomology sheaves in every integer degree
are cartesian modules. -/
theorem ModuleDerived.isCartesian_iff_homology
    (h_flat : ∀ (n : ℕ) (j : Fin (n + 2)),
      ToposHom.IsFlat (fiberRingedToposMap F J O (SimplexCategory.δ j)))
    (K : Hom.ModuleDerived.{w} (fiberTotalRingedSite F J O)) :
    ModuleDerived.IsCartesian F J O K ↔
      ∀ q : ℤ, Module.IsCartesian F J O
        (Hom.ModuleDerived.cohomologySheaf (fiberTotalRingedSite F J O) K q) := sorry

end CategoryTheory.Grothendieck
