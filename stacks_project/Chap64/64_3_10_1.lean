module

public import stacks_project.Chap64.«64_2_0_1»
import StacksCheckRecall

open AlgebraicGeometry.Scheme.Etale

/- 64.3.10.1: more precise form of the initial Grothendieck–Lefschetz trace
formula. For a finite-type scheme `X` of dimension 1 over a finite field `k`
and a constructible flat sheaf `F` of `ZMod (ℓ ^ n)`-modules, the sum of traces
of geometric Frobenius π_x on geometric stalks at `k`-points equals the
alternating sum of traces of π_X^* on compactly supported étale cohomology
H^i_c(X_k̄, F) for i = 0, 1, 2, as elements of `ZMod (ℓ ^ n)`. Here `X(k)` is
morphisms `𝟙_ ⟶ X`, π_x is `geometricFrobeniusStalk`, π_X^* is
`geometricFrobenius_cohomologyCompactSupport`, and H^i_c is
`etaleCohomologyCompactSupport`. -/
@[stacks 03SX] #check lefschetzTraceFormula
