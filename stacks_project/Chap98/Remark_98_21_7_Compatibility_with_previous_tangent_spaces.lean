/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap98.Remark_98_21_7_Compatibility_with_previous_tangent_spaces_Comparison
import StacksCheckRecall

/-!
# Compatibility with previous tangent spaces

Under condition (RS*), the predeformation tangent space `Tℱ_{X,k,x0}` and the
infinitesimal automorphism group `Inf(ℱ_{X,k,x0})` of `98.8.0.1` and `98.8.0.2`
agree as `k`-vector spaces with the RS* modules `T_{x0}(k)` and `Inf_{x0}(k)`
of Lemma 98.21.2.
-/

@[expose] public section

open AlgebraicGeometry.GroupoidsOver.Predeformation

/- Remark 98.21.7 (Compatibility with previous tangent spaces) (1). Let `S` be a
locally Noetherian scheme, let `X` be a category fibred in groupoids over
`(Sch/S)_fppf` satisfying (RS*), let `k` be a field of finite type over `S`, and
let `x0` be an object of `X` over `Spec(k)`. Then `Tℱ_{X,k,x0} = T_{x0}(k)` as
`k`-vector spaces, where the left-hand side is the dual-number fibre of
`ℱ_{X,k,x0}` as in `98.8.0.1` and the right-hand side is the value of
`tangentFunctor` at `k`. Lean records the identification as `tangentSpaceEquiv`. -/
@[stacks 0D18] #check tangentSpaceEquiv

/- Remark 98.21.7 (Compatibility with previous tangent spaces) (2). In the same
setting, `Inf(ℱ_{X,k,x0}) = Inf_{x0}(k)` as `k`-vector spaces, where the
left-hand side is the kernel of restriction on automorphisms of a cartesian
dual-number pullback as in `98.8.0.2` and the right-hand side is the value of
`infFunctor` at `k`. Lean records the identification as `infinitesimalAutEquiv`. -/
@[stacks 0D18] #check infinitesimalAutEquiv
