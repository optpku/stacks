module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Dimension.Range
import StacksCheckRecall

/-!
# Dimension of a locally Noetherian algebraic stack: value range

A nonempty algebraic stack of finite type over a field has integer dimension.
In general the dimension of a locally Noetherian algebraic stack takes values
in the extended integers, and equals `⊥` exactly on the empty stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Remark 100.12.4: a nonempty algebraic stack of finite type over a field has
integer dimension. Every locally Noetherian algebraic stack has dimension in
the extended integers, and its dimension is minus infinity exactly when its
space of points is empty. -/
@[stacks 0AFQ] #check (AlgebraicGeometry.AlgebraicStack.dimension_mem_int :
  ∀ {k : Type u} [Field k]
    (X : GroupoidsOver (Spec (.of k))) [AlgebraicStack X]
    [IsLocallyNoetherian X] [IsQuasiCompact X] [Nonempty (Points X)],
    (∃ (U : Over (Spec (.of k))) (p : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
        AlgebraicGeometry.LocallyOfFiniteType U.hom) →
    ∃ n : ℤ, dimension X = n)

#check (AlgebraicGeometry.AlgebraicStack.dimension_trichotomy :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsLocallyNoetherian X],
    dimension X = ⊥ ∨ (∃ n : ℤ, dimension X = n) ∨ dimension X = ⊤)

#check (AlgebraicGeometry.AlgebraicStack.dimension_eq_bot_iff :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsLocallyNoetherian X],
    dimension X = ⊥ ↔ IsEmpty (Points X))

end AlgebraicGeometry.AlgebraicStack
