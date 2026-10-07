module

public import stacks_project.Chap03.Lemma_3_9_2_ObjectProperty
public import ReasLib.AlgebraicGeometry.Scheme.Reduction

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open scoped Cardinal AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Remark 3.9.3. Naive reflection of the unary formula φ_scheme(X) expressing
“X is a scheme” is useless: even if φ_scheme(X) ↔ the relativization of
φ_scheme to V_α holds for all X in V_α, this does not close Sch_α under any
scheme-theoretic operation.

Combining the pair φ_red(X, Y) expressing “Y is Scheme.reduction X” with
φ₂(X) := ∃ Y, φ_red(X, Y) does yield a useful closure. If `P` is an
`IsSmallBoundClosed` object property of schemes (the Lean stand-in for Sch_α)
and `P X`, then `P.isoClosure (reduction X)`. -/
@[stacks 000O]
theorem isoClosure_reduction {P : ObjectProperty Scheme.{u}} (hP : IsSmallBoundClosed P)
    {X : Scheme.{u}} (hX : P X) : P.isoClosure (reduction X) := sorry

end AlgebraicGeometry.Scheme
