module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Specialization
import StacksCheckRecall

/-!
# Specializations along a smooth algebraic-space chart

A specialization of points of an algebraic stack lifts through a smooth morphism
from an algebraic space, provided the generizing point has a quasi-compact
field-valued representative.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.47.1: A specialization `x' ⤳ x` of algebraic-stack points lifts
through a smooth morphism `f : U.toGroupoids ⟶ X` at every point `u` above `x`,
provided `x'` has a quasi-compact field-valued representative. The lift `u'`
satisfies `u' ⤳ u` and `Points.mapSpace f u' = x'`. -/
@[stacks 0GVZ] #check
  (AlgebraicGeometry.AlgebraicStack.exists_specializes_of_smooth :
    ∀ {S : Scheme.{u}} {U : AlgebraicSpace S} {X : GroupoidsOver S}
      [AlgebraicStack X] (f : U.toGroupoids ⟶ X) [Smooth f] {x x' : Points X},
      Specializes x' x → existsQuasiCompactFieldValuedPoint X x' →
      ∀ {u : AlgebraicSpace.Points U}, Points.mapSpace f u = x →
        ∃ u' : AlgebraicSpace.Points U,
          Specializes u' u ∧ Points.mapSpace f u' = x')

/- The equivalent hypothesis requires every field-valued representative of `x'`
to be quasi-compact. -/
#check
  (AlgebraicGeometry.AlgebraicStack.exists_specializes_of_smooth_of_forallFieldValuedPointQuasiCompact :
    ∀ {S : Scheme.{u}} {U : AlgebraicSpace S} {X : GroupoidsOver S}
      [AlgebraicStack X] (f : U.toGroupoids ⟶ X) [Smooth f] {x x' : Points X},
      Specializes x' x → forallFieldValuedPointQuasiCompact X x' →
      ∀ {u : AlgebraicSpace.Points U}, Points.mapSpace f u = x →
        ∃ u' : AlgebraicSpace.Points U,
          Specializes u' u ∧ Points.mapSpace f u' = x')

end AlgebraicGeometry.AlgebraicStack
