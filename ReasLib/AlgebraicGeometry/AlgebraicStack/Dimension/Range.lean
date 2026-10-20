module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiCompact
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

/-!
# Range of the dimension of an algebraic stack

A nonempty algebraic stack of finite type over a field has integer dimension.
The dimension of a locally Noetherian algebraic stack is an extended integer,
and is minus infinity exactly when its space of points is empty.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A nonempty quasi-compact locally Noetherian algebraic stack admitting a smooth
surjective scheme atlas locally of finite type over a field has integer dimension. -/
theorem dimension_mem_int {k : Type u} [Field k]
    (X : GroupoidsOver (Spec (.of k))) [AlgebraicStack X]
    [IsLocallyNoetherian X] [IsQuasiCompact X] [Nonempty (Points X)]
    (hfiniteType : ∃ (U : Over (Spec (.of k))) (p : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
        AlgebraicGeometry.LocallyOfFiniteType U.hom) :
    ∃ n : ℤ, dimension X = n :=
  sorry

/-- The dimension of a locally Noetherian algebraic stack is minus infinity,
an integer, or plus infinity. -/
theorem dimension_trichotomy {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsLocallyNoetherian X] :
    dimension X = ⊥ ∨ (∃ n : ℤ, dimension X = n) ∨ dimension X = ⊤ :=
  sorry

/-- A locally Noetherian algebraic stack has dimension minus infinity if and only
if its space of points is empty. -/
theorem dimension_eq_bot_iff {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsLocallyNoetherian X] :
    dimension X = ⊥ ↔ IsEmpty (Points X) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
