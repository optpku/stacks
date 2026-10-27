/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.AbelianRestriction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Injective
public import stacks_project.Chap96.Lemma_96_22_1_Restriction
import StacksCheckRecall

/-!
# Lemma 96.22.1

Restriction from an algebraic stack to a representing algebraic space preserves injective
abelian étale sheaves and K-injective complexes. Both module counterparts fail.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape
open AlgebraicGeometry.GroupoidsOver
open AlgebraicGeometry.Scheme.Etale.SmallToBig.Module
open scoped Bicategory

universe u

/- Lemma 96.22.1 (1): restriction preserves injective abelian étale sheaves. -/
@[stacks 075L]
#check (AlgebraicGeometry.GroupoidsOver.injective_restrictAbelian :
    ∀ {S : Scheme.{u}} {F : AlgebraicSpace S} {X : GroupoidsOver S}
      (e : F.toGroupoids ≌ X) [AlgebraicStack X]
      [HasSheafify X.etaleTopology AddCommGrpCat.{u}]
      [HasSheafify (AlgebraicSpace.smallEtaleTopology F) AddCommGrpCat.{u}]
      (I : Sheaf X.etaleTopology AddCommGrpCat.{u}) [Injective I],
      Injective ((restrictAbelian e).obj I))

/- Lemma 96.22.1 (2): restriction preserves unbounded K-injective abelian complexes. -/
@[stacks 075L]
#check (AlgebraicGeometry.GroupoidsOver.isKInjective_restrictAbelian :
    ∀ {S : Scheme.{u}} {F : AlgebraicSpace S} {X : GroupoidsOver S}
      (e : F.toGroupoids ≌ X) [AlgebraicStack X]
      [HasSheafify X.etaleTopology AddCommGrpCat.{u}]
      [HasSheafify (AlgebraicSpace.smallEtaleTopology F) AddCommGrpCat.{u}]
      (I : CochainComplex (Sheaf X.etaleTopology AddCommGrpCat.{u}) ℤ) [I.IsKInjective],
      CochainComplex.IsKInjective
        (((restrictAbelian e).mapHomologicalComplex (up ℤ)).obj I))

/- Lemma 96.22.1 (3): restriction of étale modules need not preserve injective objects. -/
@[stacks 075L]
#check (AlgebraicGeometry.Scheme.Etale.SmallToBig.Module.specIntegerModulePullback_not_preservesInjective :
    ¬ specIntegerModulePullback.PreservesInjectiveObjects)

/- Lemma 96.22.1 (4): restriction of étale modules need not preserve K-injective complexes. -/
@[stacks 075L]
#check (AlgebraicGeometry.Scheme.Etale.SmallToBig.Module.specIntegerModulePullback_not_preservesKInjective :
    ¬ ∀ I : CochainComplex
        (SheafOfModules.{1} (StandardTopology.Big.liftedRingedSite .etale
          (Spec (CommRingCat.of ℤ))).structureSheaf) ℤ,
      I.IsKInjective →
        CochainComplex.IsKInjective
          ((specIntegerModulePullback.mapHomologicalComplex (up ℤ)).obj I))
