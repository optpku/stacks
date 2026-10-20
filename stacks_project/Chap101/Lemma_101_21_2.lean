module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.LocallyQuasiFinite
import StacksCheckRecall

/-!
# Shrinking a locally finite-type presentation to a locally quasi-finite morphism

A locally finite-type morphism from an algebraic space to an algebraic stack
becomes locally quasi-finite after shrinking the source around the image of a
zero-dimensional point of a cartesian field fibre.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.21.2: Let `X` be an algebraic stack. Consider a cartesian diagram
where `U` is an algebraic space, `k` is a field, and `U ⟶ X` is locally of
finite type. Let `z` be a point of an algebraic-space model `F` of the
cartesian field fibre `U ×_X Spec(k)` with `dimensionAt z = 0`. Then after
replacing `U` by an open subspace containing the image of `z` in `|U|`, the
morphism `U ⟶ X` is locally quasi-finite. -/
@[stacks 06ME] #check
  (AlgebraicGeometry.AlgebraicStack.exists_openSubspace_locallyQuasiFinite_of_dimensionAt_eq_zero :
    ∀ {S : Scheme.{u}} {U : AlgebraicSpace S} {X : GroupoidsOver S}
    [AlgebraicStack X] (f : U.toGroupoids ⟶ X)
    [LocallyOfFiniteType f] (p : FieldValuedPoint X) {F : AlgebraicSpace S}
    (e : TwoFibreProduct.apex.{u + 1, u, u + 1, u} f p.hom ≌ F.toGroupoids)
    (z : AlgebraicSpace.Points F)
    (hz : AlgebraicSpace.dimensionAt z = (0 : WithBot ℕ∞)),
    ∃ W : AlgebraicSpace.OpenSubspace U,
      AlgebraicSpace.Points.map (representedFiberι e) z ∈ W.pointsSet ∧
        Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S)
          (AlgebraicSpace.toGroupoids.map W.ι ≫ f))

end AlgebraicGeometry.AlgebraicStack
