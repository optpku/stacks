/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Remark_90_7_13_Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory FormalObject
open scoped BasedFunctor

/- Remark 90.7.13: a morphism `a : ξ ⟶ η` of formal objects of a category `F`
cofibered in groupoids over `C_Λ`, with base map `f = a.base` in `Ĉ_Λ`, induces a
2-cell `underline ξ ∘ f ⟶ underline η` in the 2-category of categories over `C_Λ`.
Components at `α : S ⟶ A` are the unique CFG comparisons
`β_{m,*} ξ_m ⟶ α_{m,*} η_m` over `id A`, where `m = nilpotencyIndex A`. -/
@[stacks 06SL] #check FormalObject.toRestrictedHom₂Hom
