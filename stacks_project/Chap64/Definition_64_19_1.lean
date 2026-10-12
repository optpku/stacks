/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap64.Definition_64_19_1_EulerFactor
public import stacks_project.Chap64.Definition_64_19_1_FrobeniusStalk
public import stacks_project.Chap64.Definition_64_19_1_LFunction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.SchemeOverField

/- Definition 64.19.1 (1). Let `X` be a scheme of finite type over a finite
field `k`. Let `Λ` be a finite ring of order prime to the characteristic of
`k` and `F` a constructible flat `Λ`-module on `X` étale. Then
`L(X, F) := ∏_{x ∈ |X|} det(1 - π_x^* T^{deg x} | F_x̄)⁻¹` in `Λ⟦T⟧`,
where `|X|` is the set of closed points of `X`, `deg x = [κ(x) : k]`, and
`x̄` is a geometric point lying over `x`. This is `lFunction`. -/
@[stacks 03UV] #check lFunction

/- Definition 64.19.1 (2). The same Euler product is declared for
`K ∈ D_ctf(X, Λ)`, as `lFunctionDerived`, under the stalkwise
perfectness hypothesis on geometric stalks that records finite Tor
dimension. -/
@[stacks 03UV] #check lFunctionDerived
