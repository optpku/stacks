/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.DerivedModuleSystem.Restriction
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Flat

/-!
# Descent for simplicial derived-module systems
-/

@[expose] public section

open CategoryTheory
open RingedSite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [instWeakSheafify : ∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [instLeftKan : ∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [instMorphismDiagram : IsMorphismDiagram.{u, v, w} C J]
include instMorphismDiagram instWeakSheafify instLeftKan
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ n, ToposHom.HasModulePullbackDerived (stageMorphism C J O n)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (ringedToposMap C J O φ)]

/-- If all transition morphisms of ringed topoi are flat, `K` is cartesian, and
`Hom(K_i⟦i - 1⟧, K'_i) = 0` for `i > 1`, every morphism between the derived-module
systems of `K` and `K'` is induced componentwise by a morphism `K ⟶ K'`. -/
theorem exists_hom_of_toDerivedModuleSystemHom
    (K K' : Hom.ModuleDerived.{w} (totalRingedSite C J O))
    [ModuleDerived.IsCartesian C J O K]
    (h_flat : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      ToposHom.IsFlat (ringedToposMap C J O φ))
    (h_hom : ∀ (n : SimplexCategory), 1 < n.len →
      Subsingleton
        (((toDerivedModuleSystem C J O K).obj n)⟦(n.len : ℤ) - 1⟧ ⟶
          (toDerivedModuleSystem C J O K').obj n))
    (α : RingedSite.Simplicial.DerivedModuleSystem.Hom (toDerivedModuleSystem C J O K)
      (toDerivedModuleSystem C J O K')) :
    ∃ f : K ⟶ K', ∀ n, (toDerivedModuleSystemMap C J O f).app n = α.app n := sorry

/-- A cartesian derived-module system with flat transition morphisms of ringed topoi
and `Hom(K_i⟦t⟧, K_i) = 0` for every stage `i` and `t > 0` is the system of a
cartesian derived module, via a system morphism invertible in every component. -/
theorem exists_isCartesian_of_derivedModuleSystem
    (Ksys : RingedSite.Simplicial.DerivedModuleSystemOnComponents C J O)
    (h_cartesian : RingedSite.Simplicial.DerivedModuleSystem.IsCartesian Ksys)
    (h_flat : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      ToposHom.IsFlat (ringedToposMap C J O φ))
    (h_hom : ∀ (n : SimplexCategory) (t : ℤ), 0 < t →
      Subsingleton ((Ksys.obj n)⟦t⟧ ⟶ Ksys.obj n)) :
    ∃ (K : Hom.ModuleDerived.{w} (totalRingedSite C J O))
      (α : RingedSite.Simplicial.DerivedModuleSystem.Hom (toDerivedModuleSystem C J O K) Ksys),
      ModuleDerived.IsCartesian C J O K ∧ ∀ n, IsIso (α.app n) := sorry

end CategoryTheory.SimplicialSites
