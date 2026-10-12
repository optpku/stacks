/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Remark_90_7_9_HomEquiv
public import stacks_project.Chap90.Remark_90_7_9_Restrict
public import stacks_project.Chap90.Remark_90_7_9_Unit
import StacksCheckRecall

@[expose] public section

open CategoryTheory CofiberedCategoryOver.Groupoids
open scoped BasedFunctor

/- Remark 90.7.9: the completion functor of Remark 90.7.8 and the restriction functor
`|_{C_Λ} : Cof(Ĉ_Λ) ⥤ Cof(C_Λ)` are 2-adjoint in the hom-category sense. For `F` over
`C_Λ` and `G` over `Ĉ_Λ` there is an equivalence
`Φ : Mor_{C_Λ}(G|_{C_Λ}, F) ⥤ Mor_{Ĉ_Λ}(G, hat F)` sending `φ` to the composite of the
unit `G ⟶ hat(G|_{C_Λ})` with `hat(φ)`, with quasi-inverse `Ψ` sending `ψ` to
`ψ|_{C_Λ}` postcomposed with the counit `can : hat F |_{C_Λ} ⟶ F`. -/
@[stacks 06HA] #check CofiberedCategoryOver.Groupoids.homEquivFunctor
