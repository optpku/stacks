/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Splitting
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 79.15.1 (1): Let `(U, R, s, t, c)` be a groupoid in algebraic spaces
over `B` and let `u ∈ |U|`. We say `R` is strongly split over `u` if there exists
an open subspace `P ⊂ R` such that `(U, P, s|_P, t|_P, c|_{P ×_{s,U,t} P})` is a
groupoid in algebraic spaces over `B`, `s|_P` and `t|_P` are finite, and
`{r ∈ |R| : s(r) = u ∧ t(r) = u} ⊂ |P|`. The choice of such a `P` is a strong
splitting of `R` over `u`. Existence is `IsStronglySplitOver`. -/
@[stacks 04RK] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.StrongSplitting :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (u : Points G.U.left), Type (u + 1))

/- Definition 79.15.1 (2): We say `R` is split over `u` if there exists an open
subspace `P ⊂ R` such that `(U, P, s|_P, t|_P, c|_{P ×_{s,U,t} P})` is a groupoid
in algebraic spaces over `B`, `s|_P` and `t|_P` are finite, and
`{g ∈ |G| : g maps to u} ⊂ |P|` where `G → U` is the stabilizer. The choice of
such a `P` is a splitting of `R` over `u`. Existence is `IsSplitOver`. -/
@[stacks 04RK] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.Splitting :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (u : Points G.U.left), Type (u + 1))

/- Definition 79.15.1 (3): We say `R` is quasi-split over `u` if there exists an
open subspace `P ⊂ R` such that `(U, P, s|_P, t|_P, c|_{P ×_{s,U,t} P})` is a
groupoid in algebraic spaces over `B`, `s|_P` and `t|_P` are finite, and
`e(u) ∈ |P|`. The choice of such a `P` is a quasi-splitting of `R` over `u`.
Existence is `IsQuasiSplitOver`. -/
@[stacks 04RK] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.QuasiSplitting :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (u : Points G.U.left), Type (u + 1))
