/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GermProperty
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Definition 66.7.5: let `S` be a scheme, let `X` be an algebraic space over `S`,
let `x` be a point of `|X|`, and let `P` be a property of germs of schemes which is
étale local. We say `X` has property `P` at `x` if any of the equivalent conditions
of Lemma 66.7.4 hold. -/
@[stacks 04RC] #check (AlgebraicGeometry.AlgebraicSpace.hasEtaleLocalAt :
  ∀ {S : Scheme.{u}} (P : GermProperty.{u}) (hP : P.IsEtaleLocal)
    (X : AlgebraicSpace S) (x : Points X), Prop)

#check (AlgebraicGeometry.AlgebraicSpace.forallEtaleAt_iff_existsEtaleAt :
  ∀ {S : Scheme.{u}} (P : GermProperty.{u}) (hP : P.IsEtaleLocal)
    (X : AlgebraicSpace S) (x : Points X),
    forallEtaleAt P X x ↔ hasEtaleLocalAt P hP X x)

#check (AlgebraicGeometry.AlgebraicSpace.existsEtaleAt_ofOver :
  ∀ {S : Scheme.{u}} (P : GermProperty.{u}) (hP : P.IsEtaleLocal)
    (T : Over S) (x : T.left),
    hasEtaleLocalAt P hP (ofOver T) (ofOver.pointsEquiv T x) ↔ P T.left x)

end AlgebraicGeometry.AlgebraicSpace
