/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.32.4 (1): an étale-local-on-source-and-target property is étale local
on the source. -/
@[stacks 04R0]
#check
  (AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget.toIsLocalAtSource :
    (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u}) →
      [AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget P] →
        P.IsLocalAtSource AlgebraicGeometry.Scheme.etalePrecoverage)

/- Lemma 35.32.4 (2): an étale-local-on-source-and-target property is étale local
on the target. -/
@[stacks 04R0]
#check
  (AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget.toIsLocalAtTarget :
    (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u}) →
      [AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget P] →
        P.IsLocalAtTarget AlgebraicGeometry.Scheme.etalePrecoverage)

/- Lemma 35.32.4 (3): an étale-local-on-source-and-target property is preserved
by postcomposition with an étale morphism. -/
@[stacks 04R0]
#check
  (AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget.toRespectsRightEtale :
    (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u}) →
      [AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget P] →
        P.RespectsRight
          (@AlgebraicGeometry.Etale :
            CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u}))

/- Lemma 35.32.4 (4): an étale-local-on-source-and-target property descends
across postcomposition with an étale morphism. -/
@[stacks 04R0]
#check
  (AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget.toHasOfPostcompEtale :
    (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u}) →
      [AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget P] →
        P.HasOfPostcompProperty
          (@AlgebraicGeometry.Etale :
            CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u}))
