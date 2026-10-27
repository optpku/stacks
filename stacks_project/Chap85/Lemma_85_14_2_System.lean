/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.DerivedModuleSystem.Restriction
public import stacks_project.Chap85.Definition_85_12_1_Cartesian
public import stacks_project.Chap85.Definition_85_14_1_System

/-!
# Derived restriction systems and their componentwise morphisms
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
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

#check (CategoryTheory.SimplicialSites.toDerivedModuleSystem C J O :
  ∀ K : Hom.ModuleDerived.{w} (totalRingedSite C J O),
    CategoryTheory.SimplicialSites.DerivedModuleSystemOnComponents C J O)

#check (CategoryTheory.SimplicialSites.toDerivedModuleSystemMap C J O :
  ∀ {K L : Hom.ModuleDerived.{w} (totalRingedSite C J O)}, (K ⟶ L) →
    CategoryTheory.SimplicialSites.DerivedModuleSystem.Hom
      (CategoryTheory.SimplicialSites.toDerivedModuleSystem C J O K)
      (CategoryTheory.SimplicialSites.toDerivedModuleSystem C J O L))

end CategoryTheory.SimplicialSites
