/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.CategoryTheory.CommSq

open CategoryTheory

universe u

namespace AlgebraicGeometry.FormallyUnramified

/-- A scheme morphism is formally unramified if and only if lifts from affine square-zero
thickenings are unique whenever they exist. -/
public theorem iff_subsingleton_liftStruct_of_affine {X S : Scheme.{u}} (f : X ⟶ S) :
    AlgebraicGeometry.FormallyUnramified f ↔
      ∀ {T T' : Scheme.{u}} [IsAffine T] [IsAffine T'] (i : T ⟶ T')
        [IsClosedImmersion i] (h_square : i.ker ^ 2 = 0) (g : T ⟶ X) (h : T' ⟶ S)
        (sq : CommSq g i f h), Subsingleton sq.LiftStruct := sorry

/-- Lifts of a formally unramified morphism through an arbitrary first-order thickening
are unique whenever they exist. -/
public instance subsingleton_liftStruct {X S T T' : Scheme.{u}} (f : X ⟶ S)
    [FormallyUnramified f] (i : T ⟶ T') [IsFirstOrderThickening i]
    (g : T ⟶ X) (h : T' ⟶ S) (sq : CommSq g i f h) :
    Subsingleton sq.LiftStruct := sorry

end AlgebraicGeometry.FormallyUnramified
