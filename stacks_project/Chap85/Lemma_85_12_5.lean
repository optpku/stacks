/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.CartesianDescent

@[expose] public section

open CategoryTheory
open scoped Simplicial
open CategoryTheory.SimplicialSites
open RingedSite

noncomputable section

universe u v w

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
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
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ n, ToposHom.HasModulePullbackDerived (stageMorphism C J O n)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (ringedToposMap C J O φ)]


/- Lemma 85.12.5
Cartesian modules on the total simplicial site are equivalent to degree-zero modules
with an invertible coface comparison satisfying the degree-two cocycle. -/
@[stacks 07TH] #check
  (CategoryTheory.SimplicialSites.Module.cartesianEquivalence C J O :
    CategoryTheory.SimplicialSites.Module.Cartesian C J O ≌
      CategoryTheory.SimplicialSites.Module.FaceDescent C J O)

#check (CategoryTheory.SimplicialSites.Module.cartesianEquivalence_functor C J O :
  (CategoryTheory.SimplicialSites.Module.cartesianEquivalence C J O).functor =
    CategoryTheory.SimplicialSites.Module.toDescentFunctor C J O)

#check (CategoryTheory.SimplicialSites.Module.cartesianEquivalence_inverse C J O :
  (CategoryTheory.SimplicialSites.Module.cartesianEquivalence C J O).inverse =
    CategoryTheory.SimplicialSites.Module.ofDescentFunctor C J O)
