/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Cohomology.BigSmall
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

/-!
Lemma 59.20.3 compares cohomology on the big site `(Sch / S)_τ` with the
cohomology of the canonical restriction to the small Zariski or etale site of
`S`.  The restriction is represented by the continuous direct-image functor
attached to the corresponding small-to-big relocalization functor.
-/

/- Lemma 59.20.3 (1): cohomology on the big Zariski site agrees with the
cohomology of the restriction to the small Zariski site. -/
@[stacks 03YX] #check (AlgebraicGeometry.Scheme.cohomology_isomorphic_zariski :
    ∀
    (S : Scheme.{u})
    (F : Sheaf S.bigZariskiTopology AddCommGrpCat.{u}) (p : ℕ)
    [HasSheafify S.smallZariskiTopology AddCommGrpCat.{u}]
    [HasSheafify S.bigZariskiTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.smallZariskiTopology AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf S.bigZariskiTopology AddCommGrpCat.{u})],
    IsIsomorphic
      (CategoryTheory.Sheaf.H'
        (((Zariski.SmallToBig.relocalizationFunctor (𝟙 S)).sheafPushforwardContinuous
            AddCommGrpCat.{u} S.smallZariskiTopology S.bigZariskiTopology).obj F)
        p (MorphismProperty.Over.mk _ (𝟙 S) inferInstance))
      (CategoryTheory.Sheaf.H' F p
        ((Zariski.SmallToBig.relocalizationFunctor (𝟙 S)).obj
          (MorphismProperty.Over.mk _ (𝟙 S) inferInstance))))

/- Lemma 59.20.3 (2): cohomology on the big etale site agrees with the
cohomology of the restriction to the small etale site. -/
@[stacks 03YX] #check (AlgebraicGeometry.Scheme.cohomology_isomorphic_etale :
    ∀
    (S : Scheme.{u})
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
