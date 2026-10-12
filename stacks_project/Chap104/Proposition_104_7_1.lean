/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap104.Proposition_104_7_1_Adjunction
public import stacks_project.Chap104.Proposition_104_7_1_Pullback
import StacksCheckRecall

/-!
# Proposition 104.7.1

A morphism of algebraic stacks induces a commutative square relating
`D_{LQCoh^{fbc}}` and `D(𝒪)` via exact `f^*`. The composite
`q_X ∘ f^*` is left derivable along `q_Y`, yielding
`Lf^*_QCoh : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)`. If `f` is quasi-compact and
quasi-separated, this functor is Hom-adjoint to `Rf_{QCoh,*}` for
objects of `D⁺_QCoh(𝒪_X)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)

/- Proposition 104.7.1 (1): the exact functor `f^*` induces a commutative
square relating `D_{LQCoh^{fbc}}(𝒪)` and `D(𝒪)`, with vertical arrows
`f^*`. -/
@[stacks 07BE]
#check (DerivedLQCohFbc.inverseImage_comp_inclusion f)

/- Proposition 104.7.1 (2): the composite
`D_{LQCoh^{fbc}}(𝒪_Y) ⥤ D_{LQCoh^{fbc}}(𝒪_X) ⥤ D_QCoh(𝒪_X)` is left
derivable along `q_Y`, and `Lf^*_QCoh` is its left derived functor. -/
@[stacks 07BE]
#check (DerivedQCoh.pullback f)

variable [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
variable (A : DerivedQCoh Y) (B : DerivedQCoh.Plus X)

/- Proposition 104.7.1 (3): if `f` is quasi-compact and quasi-separated, then
Hom_{D_QCoh(X)}(Lf^*_QCoh A, B) identifies with
Hom_{D_QCoh(Y)}(A, Rf_{QCoh,*} B) for `A` in `D_QCoh(𝒪_Y)` and `B` in
`D⁺_QCoh(𝒪_X)`. -/
@[stacks 07BE]
#check (DerivedQCoh.pullback_homEquiv f A B)

end AlgebraicGeometry.AlgebraicStack
