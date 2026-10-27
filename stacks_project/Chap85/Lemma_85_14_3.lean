/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.DerivedModuleSystem.Cocycle
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.DerivedModuleSystem.FiberCocycle
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite RingedSite
open scoped Simplicial

universe u v w

section Continuous

open CategoryTheory.SimplicialSites
open RingedSite.Simplicial.DerivedModuleSystem

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram.{u, v, w} C J]
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (ringedToposMap C J O φ)]


#check (CategoryTheory.SimplicialSites.DerivedModuleSystem.ofCocycleOnComponents C J O :
    ∀ (K0 : RingedSite.Hom.ModuleDerived.{w} (componentRingedSite C J O ⦋0⦌))
    (α : (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2))).modulePullbackDerived.obj K0 ≅
      (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2))).modulePullbackDerived.obj K0)
    (h : cocycleLeft (fun n ↦ componentRingedSite C J O n) (fun φ ↦ ringedToposMap C J O φ) (modulePullbackFunctoriality C J O) α =
      cocycleRight (fun n ↦ componentRingedSite C J O n) (fun φ ↦ ringedToposMap C J O φ) (modulePullbackFunctoriality C J O) α),
    RingedSite.Simplicial.DerivedModuleSystem (fun n ↦ componentRingedSite C J O n) (fun φ ↦ ringedToposMap C J O φ) (modulePullbackFunctoriality C J O))

/- Lemma 85.14.3: a coface cocycle determines a cartesian derived-module system,
whose degree-n object is the last-vertex derived pullback and whose transitions
are the specified edge-pullback composites. -/
@[stacks 0GMF] #check (CategoryTheory.SimplicialSites.DerivedModuleSystem.ofCocycleOnComponents_isCartesian C J O :
    ∀ (K0 : RingedSite.Hom.ModuleDerived.{w} (componentRingedSite C J O ⦋0⦌))
    (α : (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2))).modulePullbackDerived.obj K0 ≅
      (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2))).modulePullbackDerived.obj K0)
    (h : cocycleLeft (fun n ↦ componentRingedSite C J O n) (fun φ ↦ ringedToposMap C J O φ) (modulePullbackFunctoriality C J O) α =
      cocycleRight (fun n ↦ componentRingedSite C J O n) (fun φ ↦ ringedToposMap C J O φ) (modulePullbackFunctoriality C J O) α),
    RingedSite.Simplicial.DerivedModuleSystem.IsCartesian
      (CategoryTheory.SimplicialSites.DerivedModuleSystem.ofCocycleOnComponents C J O K0 α h))

end Continuous

section Fiberwise

open CategoryTheory.Grothendieck
open RingedSite.Simplicial.DerivedModuleSystem

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

variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (fiberRingedToposMap F J O φ).structureMap).IsRightAdjoint]

variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (fiberRingedToposMap F J O φ)]

#check (CategoryTheory.Grothendieck.DerivedModuleSystem.ofCocycleOnComponents F J O :
    ∀ (K0 : RingedSite.Hom.ModuleDerived.{w} (fiberComponentRingedSite F J O ⦋0⦌))
    (α : (fiberRingedToposMap F J O (SimplexCategory.δ (1 : Fin 2))).modulePullbackDerived.obj K0 ≅
      (fiberRingedToposMap F J O (SimplexCategory.δ (0 : Fin 2))).modulePullbackDerived.obj K0)
    (h : cocycleLeft (fun n ↦ fiberComponentRingedSite F J O n) (fun φ ↦ fiberRingedToposMap F J O φ) (modulePullbackFunctoriality F J O) α =
      cocycleRight (fun n ↦ fiberComponentRingedSite F J O n) (fun φ ↦ fiberRingedToposMap F J O φ) (modulePullbackFunctoriality F J O) α),
    RingedSite.Simplicial.DerivedModuleSystem (fun n ↦ fiberComponentRingedSite F J O n) (fun φ ↦ fiberRingedToposMap F J O φ) (modulePullbackFunctoriality F J O))

/- Lemma 85.14.3: a coface cocycle determines a cartesian derived-module system,
whose degree-n object is the last-vertex derived pullback and whose transitions
are the specified edge-pullback composites. -/
@[stacks 0GMF] #check (CategoryTheory.Grothendieck.DerivedModuleSystem.ofCocycleOnComponents_isCartesian F J O :
    ∀ (K0 : RingedSite.Hom.ModuleDerived.{w} (fiberComponentRingedSite F J O ⦋0⦌))
    (α : (fiberRingedToposMap F J O (SimplexCategory.δ (1 : Fin 2))).modulePullbackDerived.obj K0 ≅
      (fiberRingedToposMap F J O (SimplexCategory.δ (0 : Fin 2))).modulePullbackDerived.obj K0)
    (h : cocycleLeft (fun n ↦ fiberComponentRingedSite F J O n) (fun φ ↦ fiberRingedToposMap F J O φ) (modulePullbackFunctoriality F J O) α =
      cocycleRight (fun n ↦ fiberComponentRingedSite F J O n) (fun φ ↦ fiberRingedToposMap F J O φ) (modulePullbackFunctoriality F J O) α),
    RingedSite.Simplicial.DerivedModuleSystem.IsCartesian
      (CategoryTheory.Grothendieck.DerivedModuleSystem.ofCocycleOnComponents F J O K0 α h))

end Fiberwise

