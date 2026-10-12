/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import stacks_project.Chap95.Remark_95_14_6_Descent
public import stacks_project.Chap110.Lemma_110_52_1_Principal

/-!
# Remark 95.14.6

The functor `p : G-Principal ⟶ (Sch/S)_fppf` is a stack in groupoids, up to the
small-fiber replacement of Remark 8.4.9. Effective fppf descent of principal
homogeneous spaces reduces the remaining gap to a set-theoretic size condition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupAlgebraicSpace

noncomputable section

universe u v

namespace AlgebraicGeometry.GroupAlgebraicSpace.Principal

/- Remark 95.14.6 (1): we conjecture that, up to a replacement as in
Remark 8.4.9, the functor `p : G-Principal ⟶ (Sch/S)_fppf` given by
`Principal.forget` is a stack in groupoids over `(Sch/S)_fppf`. -/
@[stacks 04UP]
#check @instIsStackInGroupoids

/-- Remark 8.4.9 condition (4): the fibre of `Principal.forget G` over `U` is
essentially small, so a small model exists via `StackOver.SmallModel`. -/
theorem fibers_essentiallySmall {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (U : Over S) :
    ObjectProperty.EssentiallySmall.{u}
      (⊤ : ObjectProperty ((forget G).Fiber U)) := sorry

namespace DescentDatum

/-- Remark 95.14.6 (2): given an fppf covering `{U_i ⟶ U}_{i ∈ I}` in
`(Sch/S)_fppf`, a group algebraic space `H` over `U`, principal homogeneous
`H_{U_i}`-spaces `X_i` over `U_i`, and `H`-equivariant isomorphisms `φ_ij`
satisfying the cocycle condition, there exists a principal homogeneous `H`-space
over `U` recovering `(X_i, φ_ij)`. The hypothesis `[Small.{u} I]` is the size
condition of Spaces, Lemma 65.8.4, as in Bootstrap, Lemma 80.11.8. -/
@[stacks 04UP]
theorem exists_principalHomogeneous {U : Scheme.{u}} {I : Type v} [Small.{u} I]
    {Ui : I → Over U} {H : GroupAlgebraicSpace (ofOver (Over.mk (𝟙 U)))}
    (D : DescentDatum Ui H) : Nonempty D.Effectiveness := sorry

end DescentDatum

end AlgebraicGeometry.GroupAlgebraicSpace.Principal
