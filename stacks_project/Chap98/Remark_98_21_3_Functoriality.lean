module

public import stacks_project.Chap98.Remark_98_21_3_Functoriality_Pullback
public import stacks_project.Chap98.Remark_98_21_3_Functoriality_Map
import StacksCheckRecall

/-!
# Functoriality of infinitesimal and tangent modules

Under condition (RS*), a ring map `A ⟶ B` with `y = x|_Spec(B)` and an
`A`-linear map `M ⟶ N` induce a pullback of lift categories along
`A[M] ⟶ B[N]`, hence `A`-linear maps `Inf_x(M) ⟶ Inf_y(N)` and
`T_x(M) ⟶ T_y(N)`. A morphism of deformation situations likewise yields a
pullback of lifts, and the Inf comparison and tangent action are natural in
the square.
-/

@[expose] public section

open AlgebraicGeometry.GroupoidsOver

/- Remark 98.21.3 (Functoriality) (1). Assumptions and notation as in
Lemma 98.21.2. A ring map `A ⟶ B` with a fibre morphism `φ : x|_Spec(B) ⟶ y`
and a commutative square of `S`-algebra thickenings induce a pullback functor
`Lift(x, A') ⥤ Lift(y, B')`. The identity `φ` recovers `y = x|_Spec(B)`, and
the trivial-square-zero square specialises this to
`Lift(x, A[M]) ⥤ Lift(y, B[N])`. Lean records the pullback as `liftPullback`. -/
@[stacks 07YA] #check liftPullback

/- Remark 98.21.3 (Functoriality) (2). The same data with an `A`-linear map
`M ⟶ N` induce a canonical `A`-linear map `Inf_x(M) ⟶ Inf_y(N)`, recorded as
`infMap`. -/
@[stacks 07YA] #check infMap

/- Remark 98.21.3 (Functoriality) (3). The same data induce a canonical
`A`-linear map `T_x(M) ⟶ T_y(N)`, recorded as `tangentMap`. -/
@[stacks 07YA] #check tangentMap

/- Remark 98.21.3 (Functoriality) (4). For a square-zero thickening `A' ⟶ A`
with kernel `I`, a given lift `x'` of `x` to `A'` (which may not always exist),
and `y'` the pullback of `x'`, the diagram comparing `Inf_x(I) ≅ Inf(x'/x)`
with `Inf_y(J) ≅ Inf(y'/y)` commutes. Lean records this as `infIso_natural`. -/
@[stacks 07YA] #check infIso_natural

/- Remark 98.21.3 (Functoriality) (5). The action `T_x(I) × Lift(x, A') ⟶
Lift(x, A')` is natural in the same square, recorded as
`tangentAction_natural`. -/
@[stacks 07YA] #check tangentAction_natural
