/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.ValuativeCriterion.CommSq
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry

universe u

/- 32.15.3.1: a valuative square for `X' ⟶ Pⁿ_S` and a commutative square from
`X' ⟶ Pⁿ_S` to `X ⟶ S` determine the outer valuative square for `X ⟶ S`. -/
@[stacks 05M3] #check
  (AlgebraicGeometry.ValuativeCommSq.map :
    {X₁ Y₁ X₂ Y₂ : Scheme.{u}} → {f₁ : X₁ ⟶ Y₁} → ValuativeCommSq f₁ →
      {g : X₁ ⟶ X₂} → {h : Y₁ ⟶ Y₂} → {f₂ : X₂ ⟶ Y₂} →
        CommSq f₁ g h f₂ → ValuativeCommSq f₂)

section

variable {X₁ Y₁ X₂ Y₂ : Scheme.{u}} {f₁ : X₁ ⟶ Y₁}
variable (sq : ValuativeCommSq f₁) {g : X₁ ⟶ X₂} {h : Y₁ ⟶ Y₂} {f₂ : X₂ ⟶ Y₂}
variable (w : CommSq f₁ g h f₂)

/- Existence of the first dotted arrow `Spec sq.R ⟶ X₂` is the lifting property of the
transported outer square. -/
#check ((sq.map w).commSq.HasLift : Prop)

/- A chosen first dotted arrow is a lift of the transported outer square. -/
#check ((sq.map w).commSq.LiftStruct : Type u)

variable (l : (sq.map w).commSq.LiftStruct)

/- The first dotted arrow supplies the lower map of the valuative square over `g`. -/
#check (sq.leftOfMapLift w l : ValuativeCommSq g)

/- Existence of the second dotted arrow `Spec sq.R ⟶ X₁` is the lifting property of the
induced left-hand square. -/
#check ((sq.leftOfMapLift w l).commSq.HasLift : Prop)

/- A chosen second dotted arrow is a lift of the induced left-hand square. -/
#check ((sq.leftOfMapLift w l).commSq.LiftStruct : Type u)

end
