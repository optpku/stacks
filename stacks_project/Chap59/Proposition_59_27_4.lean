/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Cohomology.BigSmall
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

/- Proposition 59.27.4: the restriction of an abelian sheaf from the big
   étale site of a scheme to its small étale site is a sheaf, and their
   étale cohomology agrees in every degree. -/
@[stacks 03PJ] #check (AlgebraicGeometry.Scheme.cohomology_isomorphic_etale :
    ∀ (S : Scheme.{u})
      (F : Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}) (p : ℕ)
      [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
      [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
      [HasExt.{u} (Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u})],
    IsIsomorphic
      (CategoryTheory.Sheaf.H'
        (((Etale.SmallToBig.relocalizationFunctor (𝟙 S)).sheafPushforwardContinuous
            AddCommGrpCat.{u} S.smallEtaleTopology (S.overGrothendieckTopology @Etale)).obj F)
        p (MorphismProperty.Over.mk _ (𝟙 S) inferInstance))
      (CategoryTheory.Sheaf.H' F p
        ((Etale.SmallToBig.relocalizationFunctor (𝟙 S)).obj
          (MorphismProperty.Over.mk _ (𝟙 S) inferInstance))))
