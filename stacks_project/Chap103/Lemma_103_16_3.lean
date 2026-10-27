/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Quasicoherent.SiteComparison
import StacksCheckRecall

/-!
Inverse image and lower shriek give quasi-coherent comparison equivalences
for an algebraic stack and identify its quasi-coherent coreflector.
-/

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open AlgebraicGeometry.GroupoidsOver CategoryTheory

universe u

/- Lemma 103.16.3 (1)(a): inverse image and lower shriek are mutually inverse
on quasi-coherent modules for the lisse-étale inclusion. -/
@[stacks 07B1] #check
  (AlgebraicGeometry.AlgebraicStack.lisseEtaleQCohEquivalence :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
      etaleQCoh X ≌ lisseEtaleQCoh X)

/- Lemma 103.16.3 (1)(b): inverse image of a locally quasi-coherent module
with flat base change is quasi-coherent on the lisse-étale site. -/
@[stacks 07B1] #check
  (AlgebraicGeometry.AlgebraicStack.lisseEtaleModuleInverseImage.obj_isQuasicoherent_of_lqcohFbc :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
      (F : etaleModules X) [IsLocallyQuasiCoherent F] [HasFlatBaseChange F],
      ((lisseEtaleModuleInverseImage X).obj F).IsQuasicoherent)

/- Lemma 103.16.3 (1)(c): the quasi-coherent coreflector is lower shriek
after inverse image for the lisse-étale inclusion. -/
@[stacks 07B1] #check
  (AlgebraicGeometry.AlgebraicStack.lisseEtaleToQCohIsoLowerShriekInverseImage :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] (F : LQCohFbc X),
      (LQCohFbc.inclusion X).obj ((QCoh.toLQCohFbc X).obj ((LQCohFbc.toQCoh X).obj F)) ≅
        (lisseEtaleModuleLowerShriek X).obj
          ((lisseEtaleModuleInverseImage X).obj ((LQCohFbc.inclusion X).obj F)))

/- Lemma 103.16.3 (2)(a): inverse image and lower shriek are mutually inverse
on quasi-coherent modules for the flat-fppf inclusion. -/
@[stacks 07B1] #check
  (AlgebraicGeometry.AlgebraicStack.flatFppfQCohEquivalence :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
      QCoh X ≌ flatFppfQCoh X)

/- Lemma 103.16.3 (2)(b): inverse image of a locally quasi-coherent module
with flat base change is quasi-coherent on the flat-fppf site. -/
@[stacks 07B1] #check
  (AlgebraicGeometry.AlgebraicStack.flatFppfModuleInverseImage.obj_isQuasicoherent_of_lqcohFbc :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] (F : FppfModules.LQCohFbc X),
      ((flatFppfModuleInverseImage X).obj ((FppfModules.inclusion X).obj F)).IsQuasicoherent)

/- Lemma 103.16.3 (2)(c): the quasi-coherent coreflector is lower shriek
after inverse image for the flat-fppf inclusion. -/
@[stacks 07B1] #check
  (AlgebraicGeometry.AlgebraicStack.flatFppfToQCohIsoLowerShriekInverseImage :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] (F : FppfModules.LQCohFbc X),
      (QCoh.inclusion X).obj
        ((LQCohFbc.toQCoh X).obj (FppfModules.LQCohFbc.restrict F)) ≅
        (flatFppfModuleLowerShriek X).obj
          ((flatFppfModuleInverseImage X).obj ((FppfModules.inclusion X).obj F)))
