/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap85.Lemma_85_3_2_Total
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

variable {F : SimplicialObject Cat.{v, u}} (J : ∀ n, Precoverage (F.obj n))
variable [Grothendieck.IsFiberwiseSite F J]

/- Lemma 85.3.2: let `C` be a simplicial object of sites whose structure maps
`u_φ : C_n ⥤ C_m` are cocontinuous and have property `P`. Then the total site
`C_total` is the Grothendieck construction of `F : SimplicialObject Cat`, with
morphisms `(φ, f)` given by `Grothendieck.Hom` (base `φ : [m] ⟶ [n]` and fiber
`f : u_φ(U) ⟶ V`) and with selected coverings the identity-degree fiber families
`Grothendieck.ofFiber`. -/
@[stacks 09WD] #check Grothendieck.precoverage F J
@[stacks 09WD] #check Grothendieck.precoverage.isStableUnderBind F J
@[stacks 09WD] #check Grothendieck.precoverage.hasPullbacks F J
@[stacks 09WD] #check Grothendieck.precoverage.hasFactoringPullbacks F J
@[stacks 09WD] #check Grothendieck.exists_ofFiber_isPullback F J
@[stacks 09WD] #check Grothendieck.precoverage.hasIsos F J
