/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Lemma_90_19_10_LinearMap
import StacksCheckRecall

/-!
# Lemma 90.19.10

A morphism `φ : ℱ ⟶ 𝒢` of categories cofibered in groupoids over `C_Λ`
satisfying (RS) induces a `k`-linear map `Inf_x0(ℱ) ⟶ Inf_φ(x0)(𝒢)` at any
residue-fibre object `x0`.
-/

@[expose] public section

open CategoryTheory

/- Lemma 90.19.10: Let φ : ℱ ⟶ 𝒢 be a morphism of categories cofibered in
groupoids over C_Λ satisfying (RS). Let x0 ∈ Ob(ℱ(k)). Then φ induces a
k-linear map Inf_x0(ℱ) ⟶ Inf_φ(x0)(𝒢). -/
@[stacks 07W6]
#check BasedFunctor.infAutLinearMap
