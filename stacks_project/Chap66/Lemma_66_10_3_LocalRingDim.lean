/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.KrullDimension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Dimension.Stalk
public import stacks_project.Chap66.Definition_66_9_2_Dimension

/-!
# Dimension of local rings of algebraic spaces

The dimension of the local ring of an algebraic space at a point is the common Krull dimension
of the stalks of étale scheme charts through that point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The dimension of the local ring of an algebraic space at a point, as the supremum of the
Krull dimensions of stalks of étale scheme charts through that point. -/
noncomputable def localRingDimAt {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) :
    WithBot ℕ∞ :=
  ⨆ (U : Over S) (f : ofOver U ⟶ X) (u : U.left)
    (_hf : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf f)
    (_hx : Points.mapOfOver f u = x), ringKrullDim (U.left.presheaf.stalk u)

/-- The dimension of the local ring at a point equals the Krull dimension of the stalk of any
étale scheme chart through that point. -/
theorem localRingDimAt_eq_ringKrullDim_stalk {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : Over S} (f : ofOver U ⟶ X)
    (hf : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf f) (u : U.left)
    {x : Points X} (hx : Points.mapOfOver f u = x) :
    localRingDimAt x = ringKrullDim (U.left.presheaf.stalk u) :=
  sorry

/-- On a scheme, viewed as an algebraic space, the dimension of the local ring at the image of a
point is the usual stalk Krull dimension. -/
theorem localRingDimAt_ofOver {S : Scheme.{u}} (T : Over S) (t : T.left) :
    localRingDimAt (ofOver.pointsEquiv T t) = ringKrullDim (T.left.presheaf.stalk t) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
