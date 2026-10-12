/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.ResidueField

@[expose] public section

/-!
Lemma 33.14.1 is a canonical recall.  Its closed-point residue-field result belongs to the
finite-type morphism API, while Jacobsonness is already owned by mathlib's
`LocallyOfFiniteType.jacobsonSpace` theorem.
-/

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 33.14.1 (1): if `X` is locally of finite type over the field `k`, then for every closed
point `x ∈ X` the residue field extension `κ(x) / k` induced by `f` is algebraic. -/
@[stacks 0478]
#check (AlgebraicGeometry.LocallyOfFiniteType.residueField_isAlgebraic_of_closedPoint :
  ∀ {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType f]
    (x : X), x ∈ closedPoints X →
      Scheme.Hom.ResidueField.IsAlgebraicOverSpec f x)

section

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType f]

/- Lemma 33.14.1 (2): if `X` is locally of finite type over the field `k`, then `X` is a
Jacobson scheme. -/
@[stacks 0478]
#check (AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace f : JacobsonSpace X)

end

end
