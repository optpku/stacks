/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Cech.CoproductSingleton
public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct.CoproductSingleton.Covering
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w v u

/- Lemma 35.9.1 (1): the singleton family on the coproduct of the sources of a finite covering
family is again covering over the same target. -/
@[stacks 03FI]
#check
  (CategoryTheory.Limits.FormalCoproduct.IsCovering.coproductSingleton :
    ∀ {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {U : C}
      (K : FormalCoproduct.{w} (Over U)) [Finite K.I]
      [HasCoproduct (fun i ↦ (K.obj i).left)],
      FormalCoproduct.IsCovering J.toPrecoverage K →
        FormalCoproduct.IsCovering J.toPrecoverage
          (FormalCoproduct.Over.coproductSingleton K))

/- Lemma 35.9.1 (2): the original family refines its singleton family on the coproduct via the
canonical coproduct inclusions. -/
@[stacks 03FI]
#check
  (CategoryTheory.Limits.FormalCoproduct.Over.toCoproductSingleton :
    ∀ {C : Type u} [Category.{v} C] {U : C}
      (K : FormalCoproduct.{w} (Over U))
      [HasCoproduct (fun i ↦ (K.obj i).left)],
      K ⟶ FormalCoproduct.Over.coproductSingleton K)

/- Lemma 35.9.1 (3): for a standard big site over a scheme, the Čech-complex map from the
coproduct-singleton family to the original finite family is an isomorphism for abelian sheaves. -/
@[stacks 03FI]
#check
  (AlgebraicGeometry.StandardTopology.coproductSingletonCechMap_isIso :
    ∀ (τ : AlgebraicGeometry.StandardTopology) (S : AlgebraicGeometry.Scheme.{u})
      (U : Over S) (K : FormalCoproduct.{u} (Over U)) [Finite K.I]
      [HasCoproduct (fun i ↦ (K.obj i).left)]
      (F : Sheaf (τ.overTopology S) AddCommGrpCat.{u}),
      IsIso (CategoryTheory.cechComplexMapOfRefinement U
        (FormalCoproduct.Over.coproductSingleton K).obj K.obj
        (FormalCoproduct.Over.toCoproductSingleton K) F.obj))

/- Lemma 35.9.1 (4): on the small étale site, the Čech-complex map from the
coproduct-singleton family to the original finite family is an isomorphism for abelian sheaves. -/
@[stacks 03FI]
#check
  (AlgebraicGeometry.Scheme.Etale.coproductSingletonCechMap_isIso :
    ∀ (S : AlgebraicGeometry.Scheme.{u}) (U : S.Etale)
      (K : FormalCoproduct.{u} (Over U)) [Finite K.I]
      [HasCoproduct (fun i ↦ (K.obj i).left)]
      (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}),
      IsIso (CategoryTheory.cechComplexMapOfRefinement U
        (FormalCoproduct.Over.coproductSingleton K).obj K.obj
        (FormalCoproduct.Over.toCoproductSingleton K) F.obj))

/- Lemma 35.9.1 (5): on the small Zariski site, the Čech-complex map from the
coproduct-singleton family to the original finite family is an isomorphism for abelian sheaves. -/
@[stacks 03FI]
#check
  (AlgebraicGeometry.Scheme.Zariski.coproductSingletonCechMap_isIso :
    ∀ (S : AlgebraicGeometry.Scheme.{u}) (U : S.smallZariskiSite)
      (K : FormalCoproduct.{u} (Over U)) [Finite K.I]
      [HasCoproduct (fun i ↦ (K.obj i).left)]
      (F : Sheaf S.smallZariskiTopology AddCommGrpCat.{u}),
      IsIso (CategoryTheory.cechComplexMapOfRefinement U
        (FormalCoproduct.Over.coproductSingleton K).obj K.obj
        (FormalCoproduct.Over.toCoproductSingleton K) F.obj))
