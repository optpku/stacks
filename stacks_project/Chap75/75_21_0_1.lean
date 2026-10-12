/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.«75_21_0_1_Comparison»
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open scoped TensorProduct

noncomputable section

universe u

variable {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
variable (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
variable (h_comm : g' ≫ f = f' ≫ g)
variable (K : DerivedQCoh X) (K' : DerivedQCoh X')
variable (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K')
variable (xbar' : GeometricPoint X') (i : ℤ)

/- 75.21.0.1: for a commutative square of algebraic spaces over `S`, `K` in `D_QCoh(𝒪_X)`,
and a map `L(g')^* K ⟶ K'` in `D_QCoh(𝒪_{X'})`, each geometric point `x̄'` of `X'` and
each `i : ℤ` determine a canonical `𝒪_{X', x̄'}`-module map
`H^i(K_{x̄} ⊗^L_{𝒪_{Y, ȳ}} 𝒪_{Y', ȳ'}) ⊗_{(𝒪_{X, x̄} ⊗_{𝒪_{Y, ȳ}} 𝒪_{Y', ȳ'})} 𝒪_{X', x̄'} ⟶ H^i(K'_{x̄'})`. -/
@[stacks 0DKF] #check
  (pointCohomologyMap g' f' f g h_comm K K' α xbar' i :
    (ModuleCat.extendScalars (pointTensorMap g' f' f g h_comm xbar').hom).obj
        ((DerivedCategory.homologyFunctor
            (ModuleCat (pointTensorRing g' f' f g h_comm xbar')) i).obj
          (stalkTensor g' f' f g h_comm K xbar')) ⟶
      (DerivedCategory.homologyFunctor (ModuleCat (etaleLocalRing X' xbar')) i).obj
        (ModuleDerived.stalkDerived xbar' ((inclusion X').obj K')))

end
