/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GermProperty
public import stacks_project.Chap66.Lemma_66_7_4_EtaleLocal

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 66.7.4 (1): an étale-local property of scheme germs holds at every étale scheme chart
through a point of an algebraic space if and only if it holds at some such chart. -/
@[stacks 04N2] #check (AlgebraicGeometry.AlgebraicSpace.forallEtaleAt_iff_existsEtaleAt :
  ∀ {S : Scheme.{u}} (P : GermProperty.{u}) (hP : P.IsEtaleLocal)
    (X : AlgebraicSpace S) (x : Points X),
    forallEtaleAt P X x ↔ existsEtaleAt P X x)

/- Lemma 66.7.4 (2): for a representable algebraic space, the chart condition is equivalent to
the property at the corresponding scheme point. -/
@[stacks 04N2] #check (AlgebraicGeometry.AlgebraicSpace.existsEtaleAt_ofOver :
  ∀ {S : Scheme.{u}} (P : GermProperty.{u}) (hP : P.IsEtaleLocal)
    (T : Over S) (x : T.left),
    existsEtaleAt P (ofOver T) (ofOver.pointsEquiv T x) ↔ P T.left x)

#check (AlgebraicGeometry.AlgebraicSpace.forallEtaleAt_ofOver :
  ∀ {S : Scheme.{u}} (P : GermProperty.{u}) (hP : P.IsEtaleLocal)
    (T : Over S) (x : T.left),
    forallEtaleAt P (ofOver T) (ofOver.pointsEquiv T x) ↔ P T.left x)

#check (AlgebraicGeometry.AlgebraicSpace.existsEtaleAt_iso :
  ∀ {S : Scheme.{u}} (P : GermProperty.{u}) (hP : P.IsEtaleLocal)
    {X : AlgebraicSpace S} {T : Over S} (e : X ≅ ofOver T) (x : Points X),
    existsEtaleAt P X x ↔
      P T.left ((ofOver.pointsEquiv T).symm (Points.map e.hom x)))

end AlgebraicGeometry.AlgebraicSpace
