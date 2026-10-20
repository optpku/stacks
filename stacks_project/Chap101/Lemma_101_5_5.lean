module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.RelativeInertia.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
import StacksCheckRecall

/-!
# Base change of relative inertia of algebraic stacks

For morphisms of algebraic stacks `π : X ⟶ Y` and `f : Y' ⟶ Y`, with
`X'` the chosen 2-fibre product `TwoFibreProduct.apex π f`, both squares in
`relativeInertia (TwoFibreProduct.snd π f) ⟶ TwoFibreProduct.apex π f ⟶ Y'`
over `relativeInertia π ⟶ X ⟶ Y` are 2-fibre products.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.RelativeInertia

variable {S : Scheme.{u}} {X Y Y' : GroupoidsOver S}
variable (π : X ⟶ Y) (f : Y' ⟶ Y)

variable [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y']

/- Lemma 101.5.5: the relative-inertia base-change square and the defining
square of the canonical two-fibre product are both fibre product squares. -/
@[stacks 06PQ] #check
  (AlgebraicGeometry.GroupoidsOver.RelativeInertia.baseChangeCone.isBilimit π f :
    (AlgebraicGeometry.GroupoidsOver.RelativeInertia.baseChangeCone π f).IsBilimit)

#check (CategoryTheory.TwoFibreProduct.cone.isBilimit.{u + 1, u, u + 1, u} π f :
  (CategoryTheory.TwoFibreProduct.cone.{u + 1, u, u + 1, u} π f).IsBilimit)

end AlgebraicGeometry.AlgebraicStack.RelativeInertia
