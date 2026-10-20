module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective.AlgClosedPoints
import StacksCheckRecall

/-!
# Surjectivity of locally finite type morphisms of algebraic spaces

A locally-of-finite-type morphism of algebraic spaces is surjective if and only
if it is surjective on algebraically closed field-valued points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.24.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `f` is locally of finite type. The following
are equivalent: `f` is surjective, and for every algebraically closed field `k`
over `S` the induced map `X(k) → Y(k)` is surjective. -/
@[stacks 0487] #check
  (AlgebraicGeometry.AlgebraicSpace.surjective_iff_surjectiveOnAlgClosedPoints :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f],
      Surjective f ↔ surjectiveOnAlgClosedPoints f)

end AlgebraicGeometry.AlgebraicSpace
