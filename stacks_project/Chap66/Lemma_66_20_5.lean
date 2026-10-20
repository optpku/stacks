/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.RingSupport

/-!
# Closedness of the support of a sheaf of rings

On the small étale site of an algebraic space, the support of a sheaf of rings is a
closed subset of `|X|`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 66.20.5: the support of a sheaf of rings on the small étale site of an algebraic
space is closed. -/
@[stacks 04KC] #check (AlgebraicGeometry.AlgebraicSpace.isClosed_ringSheafSupport :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) RingCat.{u}), IsClosed (ringSheafSupport F))

#check (AlgebraicGeometry.AlgebraicSpace.isClosed_schemePreimage_ringSheafSupport :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) RingCat.{u}) {U : Over S} (f : ofOver U ⟶ X),
    (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf f →
    IsClosed (schemePreimage f (ringSheafSupport F)))

end AlgebraicGeometry.AlgebraicSpace
