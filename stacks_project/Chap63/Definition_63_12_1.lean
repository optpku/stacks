/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap63.Definition_63_12_1_Gamma
public import stacks_project.Chap63.Definition_63_12_1_LowerShriek
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.Scheme.Etale

/- Definition 63.12.1 (1): for a separated finite-type scheme `X` over a field
`k` and a ring `Λ`, the compactly supported derived sections of an object `K`
of `D⁺_tors(X_étale, Λ)`, or of `D(X_étale, Λ)` when `Λ` is torsion, are
`RΓ_c(X, K) = RΓ(Spec k, Rf_! K)`, where `f : X.left ⟶ Spec k` is the
structure morphism. -/
@[stacks 0GJZ] #check etaleDerivedGammaCompactSupport

/- Definition 63.12.1 (2): compactly supported cohomology is
`H^i_c(X, K) = H^i(RΓ_c(X, K))`. -/
@[stacks 0GJZ] #check etaleDerivedCohomologyCompactSupport

end
