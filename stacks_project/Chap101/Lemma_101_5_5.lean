/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Lemma_101_5_5_BaseChange
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit
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

/- Lemma 101.5.5 (1): the right square `TwoFibreProduct.apex π f ⟶ Y'` over
`X ⟶ Y` is the defining 2-fibre product of `X' = TwoFibreProduct.apex π f`,
with `π' = TwoFibreProduct.snd π f`. -/
@[stacks 06PQ]
#check (TwoFibreProduct.cone.isBilimit.{u + 1, u, u + 1, u} π f :
  (TwoFibreProduct.cone.{u + 1, u, u + 1, u} π f).IsBilimit)

/-- Lemma 101.5.5 (2): the left square
`relativeInertia (TwoFibreProduct.snd π f) ⟶ TwoFibreProduct.apex π f` over
`relativeInertia π ⟶ X` is a 2-fibre product. The left vertical is Categories
Equation 04Z4, i.e. `RelativeInertia.map` along
`(TwoFibreProduct.comparisonIso π f).symm`. -/
@[stacks 06PQ, instance]
instance relativeInertia_baseChange_isBilimit
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y'] :
    (baseChangeCone π f).IsBilimit :=
  sorry

end AlgebraicGeometry.AlgebraicStack.RelativeInertia
