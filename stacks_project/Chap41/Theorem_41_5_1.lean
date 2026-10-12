/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallyUnramified.Lifting
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Noetherian
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory

universe u

/- Theorem 41.5.1: A locally finite type morphism to a locally Noetherian scheme is
unramified if and only if it is formally unramified. -/
@[stacks 024R] #check
  (AlgebraicGeometry.LocallyOfFiniteType.unramified_iff_formallyUnramified :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType f],
      Unramified f ↔ FormallyUnramified f)

/- The affine square-zero lifting characterization of formal unramifiedness. -/
#check
  (AlgebraicGeometry.FormallyUnramified.iff_subsingleton_liftStruct_of_affine :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S), FormallyUnramified f ↔
      ∀ {T T' : Scheme.{u}} [IsAffine T] [IsAffine T'] (i : T ⟶ T')
        [IsClosedImmersion i] (_ : i.ker ^ 2 = 0) (g : T ⟶ X) (h : T' ⟶ S)
        (sq : CommSq g i f h), Subsingleton sq.LiftStruct)
