module

public import stacks_project.Chap64.«64_2_0_1_GeometricFrobenius»
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry
open AlgebraicGeometry.Scheme.Etale AlgebraicGeometry.SchemeOverField

/- Definition 64.3.10: if `x : 𝟙_ ⟶ X` is a `k`-rational point of a scheme `X`
over a finite field `k`, and `x̄ : Spec(AlgebraicClosure k) ⟶ X` is the
geometric point lying over `x`, the geometric Frobenius
`π_x : F_x̄ ⟶ F_x̄` is the action of `frob_k⁻¹` on the étale stalk.
Here `x̄` is `homSpecGeometric` / `geometricPointOfHomSpec`, and `π_x` is
`geometricFrobeniusStalk`, the Galois action of `arithmeticFrobeniusEquiv`⁻¹.
This notation is not standard; SGA4.5 writes `F_x`. -/
@[stacks 03SW] #check geometricFrobeniusStalk
@[stacks 03SW] #check geometricFrobeniusStalk_apply
@[stacks 03SW] #check homSpecGeometric
@[stacks 03SW] #check geometricPointOfHomSpec
@[stacks 03SW] #check geometricPointOfHomSpec_image
