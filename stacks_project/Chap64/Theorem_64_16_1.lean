module

public import stacks_project.Chap64.«64_16_1_1»
import StacksCheckRecall

open AlgebraicGeometry.SchemeOverField

/- Theorem 64.16.1: for a finite field `k`, a finite-type separated `k`-scheme
`X` of dimension at most 1, a finite ring `Λ` with `|Λ|` coprime to `|k|`, and
`K` in `D_ctf(X, Λ)`, the compact-support Lefschetz equality
`Tr(π_X^* | RΓ_c(X_k̄, K)) = ∑_{x ∈ X(k)} Tr(π_x | K_x̄)` holds in `Λ♮`.
Here `RΓ_c` is `geometricRGammaCompactSupport` via a projective compactification,
the left-hand endomorphism is `geometricFrobeniusRGammaCompactSupport`, and
the right-hand stalk endomorphisms are `geometricFrobeniusDerivedStalk`. -/
@[stacks 03UG] #check lefschetzTraceFormula_compactSupport
