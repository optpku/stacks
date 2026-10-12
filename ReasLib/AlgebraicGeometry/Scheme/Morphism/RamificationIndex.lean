/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RamificationInertia.Ramification
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Stalk

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The ramification index of a scheme morphism at a point, computed from its induced stalk
algebra and the maximal ideal of the source stalk. -/
noncomputable def ramificationIndexAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) : ℕ :=
  @Ideal.ramificationIdx (X.presheaf.stalk x) _
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (Y.presheaf.stalk (f x)) _ (f.stalkAlgebra x)

/-- The pointwise ramification index is the corresponding `Ideal.ramificationIdx` expression. -/
theorem ramificationIndexAt_eq_ramificationIdx {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    f.ramificationIndexAt x =
      @Ideal.ramificationIdx (X.presheaf.stalk x) _
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (Y.presheaf.stalk (f x)) _ (f.stalkAlgebra x) := sorry

end AlgebraicGeometry.Scheme.Hom
