module

public import stacks_project.Chap98.Situation_98_24_2_DualObstruction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.GroupoidsOver

/- Situation 98.24.2: let S be a locally Noetherian scheme and let X be a
category fibred in groupoids over (Sch/S)_fppf with (RS*), so that the functor
T_x(-) is available. Let U = Spec(A) be affine of finite type over S, mapping
into an affine open Spec(Λ), and let x be an object of X over U. Dual
obstruction data at this x consists of a complex K of A-modules, an
isomorphism T_x(-) ≅ H^1(K ⊗^L_A -), and obstruction classes
o_x(A') ∈ H^2(K ⊗^L_A I) for deformation situations (x, A' → A), natural in
square-zero extensions of A with identity on x and vanishing if and only if x
lifts. Infinitesimal automorphisms Inf_x ≅ H^0(K ⊗^L_A -) are deliberately
omitted. Lean records this situation as DualObstruction. -/
@[stacks 07YX]
#check DualObstruction

#check DualObstruction.of

#check DualObstruction.spec

#check DualObstruction.obstruction_eq_zero_iff_nonempty_objectLift
