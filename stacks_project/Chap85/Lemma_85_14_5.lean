/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.DerivedHom
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.FiberDerivedHom

@[expose] public section

open CategoryTheory
open scoped Simplicial
open RingedSite
open Opposite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [instWeakSheafify : ∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [instLeftKan : ∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [instMorphismDiagram : IsMorphismDiagram C J]
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

/- Lemma 85.14.5 (1). The nullity criterion for the continuous site presentation. -/
@[stacks 0D9R] #check (CategoryTheory.SimplicialSites.ModuleDerived.hom_eq_zero C J O :
    ∀ (K K' : Hom.ModuleDerived.{w} (totalRingedSite C J O))
    [ModuleDerived.IsCartesian C J O K]
    (h_flat : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      ToposHom.IsFlat (ringedToposMap C J O φ))
    (h_hom : ∀ n : SimplexCategory, 0 < n.len →
      Subsingleton (((moduleDerivedComponent C J O n).obj K)⟦(n.len : ℤ)⟧ ⟶
        (moduleDerivedComponent C J O n).obj K'))
    (h_hom_succ : ∀ n : SimplexCategory,
      Subsingleton (((moduleDerivedComponent C J O n).obj K)⟦(n.len + 1 : ℤ)⟧ ⟶
        (moduleDerivedComponent C J O n).obj K'))
    (f : K ⟶ K') (hf0 : (moduleDerivedComponent C J O ⦋0⦌).map f = 0),
    f = 0)

/- Morphisms agreeing on the degree-zero component are equal under the same hypotheses. -/
#check (CategoryTheory.SimplicialSites.ModuleDerived.hom_ext C J O :
    ∀ (K K' : Hom.ModuleDerived.{w} (totalRingedSite C J O))
    [ModuleDerived.IsCartesian C J O K]
    (h_flat : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      ToposHom.IsFlat (ringedToposMap C J O φ))
    (h_hom : ∀ n : SimplexCategory, 0 < n.len →
      Subsingleton (((moduleDerivedComponent C J O n).obj K)⟦(n.len : ℤ)⟧ ⟶
        (moduleDerivedComponent C J O n).obj K'))
    (h_hom_succ : ∀ n : SimplexCategory,
      Subsingleton (((moduleDerivedComponent C J O n).obj K)⟦(n.len + 1 : ℤ)⟧ ⟶
        (moduleDerivedComponent C J O n).obj K'))
    (f g : K ⟶ K')
    (hfg : (moduleDerivedComponent C J O ⦋0⦌).map f =
      (moduleDerivedComponent C J O ⦋0⦌).map g),
    f = g)

end CategoryTheory.SimplicialSites

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

/- Lemma 85.14.5 (2). The nullity criterion for the fiberwise site presentation. -/
@[stacks 0D9R] #check (CategoryTheory.Grothendieck.ModuleDerived.hom_eq_zero F J O :
    ∀ (K K' : Hom.ModuleDerived.{w} (fiberTotalRingedSite F J O))
    [ModuleDerived.IsCartesian F J O K]
    (h_flat : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      ToposHom.IsFlat (fiberRingedToposMap F J O φ))
    (h_hom : ∀ n : SimplexCategory, 0 < n.len →
      Subsingleton (((moduleDerivedComponent F J O n).obj K)⟦(n.len : ℤ)⟧ ⟶
        (moduleDerivedComponent F J O n).obj K'))
    (h_hom_succ : ∀ n : SimplexCategory,
      Subsingleton (((moduleDerivedComponent F J O n).obj K)⟦(n.len + 1 : ℤ)⟧ ⟶
        (moduleDerivedComponent F J O n).obj K'))
    (f : K ⟶ K') (hf0 : (moduleDerivedComponent F J O ⦋0⦌).map f = 0),
    f = 0)

end CategoryTheory.Grothendieck
