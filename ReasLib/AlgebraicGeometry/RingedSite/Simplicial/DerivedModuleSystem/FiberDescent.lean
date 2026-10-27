/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.DerivedModuleSystem.FiberRestriction
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Flat

/-!
# Descent for derived-module systems on fibers
-/

@[expose] public section

open CategoryTheory Opposite
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

/-- A cartesian derived-module system on the fibers with flat transition morphisms
of ringed topoi and `Hom(K_i⟦t⟧, K_i) = 0` for every stage `i` and `t > 0` is
the system of a cartesian derived module on the total site, via a system morphism
invertible in every component. -/
theorem exists_isCartesian_of_derivedModuleSystem
    (Ksys : DerivedModuleSystemOnComponents F J O)
    (h_cartesian : RingedSite.Simplicial.DerivedModuleSystem.IsCartesian Ksys)
    (h_flat : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      RingedSite.ToposHom.IsFlat (fiberRingedToposMap F J O φ))
    (h_hom : ∀ (n : SimplexCategory) (t : ℤ), 0 < t →
      Subsingleton ((Ksys.obj n)⟦t⟧ ⟶ Ksys.obj n)) :
    ∃ (K : RingedSite.Hom.ModuleDerived.{w} (fiberTotalRingedSite F J O))
      (α : RingedSite.Simplicial.DerivedModuleSystem.Hom (toDerivedModuleSystem F J O K) Ksys),
      ModuleDerived.IsCartesian F J O K ∧ ∀ n, IsIso (α.app n) := sorry

/-- If the transition morphisms of ringed topoi are flat, `K` is cartesian, and
`Hom(K_i⟦i - 1⟧, K'_i) = 0` for `i > 1`, every morphism between their fiberwise
derived-module systems is induced componentwise by a morphism `K ⟶ K'`. -/
theorem exists_hom_of_toDerivedModuleSystemHom
    (K K' : Hom.ModuleDerived.{w} (fiberTotalRingedSite F J O))
    [ModuleDerived.IsCartesian F J O K]
    (h_flat : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      ToposHom.IsFlat (fiberRingedToposMap F J O φ))
    (h_hom : ∀ (n : SimplexCategory), 1 < n.len →
      Subsingleton
        (((toDerivedModuleSystem F J O K).obj n)⟦(n.len : ℤ) - 1⟧ ⟶
          (toDerivedModuleSystem F J O K').obj n))
    (α : RingedSite.Simplicial.DerivedModuleSystem.Hom (toDerivedModuleSystem F J O K)
      (toDerivedModuleSystem F J O K')) :
    ∃ f : K ⟶ K', ∀ n, (toDerivedModuleSystemMap F J O f).app n = α.app n := sorry

end CategoryTheory.Grothendieck
