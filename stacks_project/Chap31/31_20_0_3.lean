/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.SectionSequence.AssociatedGraded
import StacksCheckRecall

/-!
# Polynomial map to an associated graded stalk ring

The germs of a finite family of sections generate an ideal in every stalk and determine a
polynomial map to the associated graded ring of that ideal.
-/

@[expose] public section

universe u

open Opposite TopologicalSpace
open AlgebraicGeometry.RingedSpace.SectionSequence

/- 31.20.0.3: the variables associated to a finite family of sections map to the degree-one
classes of their germs in the associated graded ring of the generated stalk ideal. -/
@[stacks 063B]
#check (AlgebraicGeometry.RingedSpace.SectionSequence.stalkAssociatedGradedMap :
  {X : AlgebraicGeometry.RingedSpace.{u}} → {U : Opens X} → {r : ℕ} →
    (f : Fin r → X.presheaf.obj (op U)) → (x : X) → (hx : x ∈ U) →
      MvPolynomial (Fin r) (X.presheaf.stalk x ⧸ germIdeal f x hx)
        →ₐ[X.presheaf.stalk x ⧸ germIdeal f x hx]
          Ideal.AssociatedGraded.ring (germIdeal f x hx))

#check (AlgebraicGeometry.RingedSpace.SectionSequence.stalkAssociatedGradedMap_X :
  ∀ {X : AlgebraicGeometry.RingedSpace.{u}} {U : Opens X} {r : ℕ}
    (f : Fin r → X.presheaf.obj (op U)) (x : X) (hx : x ∈ U) (i : Fin r),
      stalkAssociatedGradedMap f x hx (MvPolynomial.X i) =
        Ideal.AssociatedGraded.degreeOne (germGenerator f x hx i))
