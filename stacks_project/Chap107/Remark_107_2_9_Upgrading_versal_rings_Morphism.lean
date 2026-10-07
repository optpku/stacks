module

public import stacks_project.Chap98.«98_9_3_1»
public import stacks_project.Chap107.Definition_107_4_1_VersalRing

/-!
# Complete local objects realizing a versal ring

A complete local object of `X` realizes a versal ring `A` at a finite type
field-valued point when it lies over `Spec(A)` and its approximation is
isomorphic to a versal formal object on the same carrier `A`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}

/-- A complete local object `x` of `X` realizes a versal ring `A` at a finite
type field-valued point `x0` when `x` lies over `Spec(A)` and the approximation
of `x` is isomorphic to a versal formal object of `X` on `A` whose first stage
is 2-isomorphic to `x0`. -/
def RealizesVersalRing (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A : CompleteLocalSAlgebra S) (x : CompleteLocalObject X) : Prop :=
  x.base = A ∧
    ∃ ξ : FormalObject X,
      ξ.base = A ∧ StageOneCompatible x0 ξ ∧ GroupoidsOver.FormalObject.IsVersal ξ ∧
        Nonempty ((approximation X).obj x ≅ ξ)

namespace RealizesVersalRing

/-- Realizing a versal ring unpacks to the same-carrier condition and a versal
formal object on `A` isomorphic to the approximation of `x`. -/
theorem spec (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A : CompleteLocalSAlgebra S) (x : CompleteLocalObject X)
    (h : RealizesVersalRing x0 A x) :
    x.base = A ∧
      ∃ ξ : FormalObject X,
        ξ.base = A ∧ StageOneCompatible x0 ξ ∧ GroupoidsOver.FormalObject.IsVersal ξ ∧
          Nonempty ((approximation X).obj x ≅ ξ) :=
  sorry

/-- Realizing a versal ring is the same-carrier condition together with a versal
formal object on `A` isomorphic to the approximation of `x`. -/
theorem iff (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A : CompleteLocalSAlgebra S) (x : CompleteLocalObject X) :
    RealizesVersalRing x0 A x ↔
      x.base = A ∧
        ∃ ξ : FormalObject X,
          ξ.base = A ∧ StageOneCompatible x0 ξ ∧ GroupoidsOver.FormalObject.IsVersal ξ ∧
            Nonempty ((approximation X).obj x ≅ ξ) :=
  sorry

/-- A complete local object realizing `A` at `x0` implies that `A` is a versal
ring to `X` at `x0`. -/
theorem toIsVersalRing [AlgebraicStack X] (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A : CompleteLocalSAlgebra S) (x : CompleteLocalObject X)
    (hx : RealizesVersalRing x0 A x) : IsVersalRing x0 A :=
  sorry

end RealizesVersalRing

end AlgebraicGeometry.AlgebraicStack
