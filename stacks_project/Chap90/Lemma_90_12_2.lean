/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Lemma_90_12_2_SquareZero
public import stacks_project.Chap90.Lemma_90_12_2_Tensor
import StacksCheckRecall

/-!
# Lemma 90.12.2

If `F` is a predeformation category whose associated isomorphism-class functor
`F-bar` satisfies (S2), then `T F` carries a natural `k`-vector space structure,
and `F-bar(k[V])` identifies with `T F ⊗[k] V` functorially in every finite-dimensional
`k`-vector space `V`.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.Functor
open ArtinianLocalAlgCat
open scoped TensorProduct

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k)
variable [IsPredeformationCategory p] [HasSchlessingerH2 (fiberIsoClassFunctor p)]

/- Lemma 90.12.2 (1): Let `F` be a predeformation category such that
`F-bar` satisfies (S2). Then `T F` has a natural `k`-vector space structure. -/
@[stacks 06IH]
#check (instModule_fiberDualTangent p :
    Module k ((fiberIsoClassFunctor p).obj (dualNumber Λ k)))

variable (V : FGModuleCat.{u} k)

/-- Lemma 90.12.2 (2): For any finite-dimensional `k`-vector space `V` we have
`F-bar(k[V]) = T F ⊗[k] V` functorially in `V`, via the canonical comparison
`fiberDualTangentTensor p V`. -/
@[stacks 06IH]
theorem bijective_fiberDualTangentTensor :
    Function.Bijective (fiberDualTangentTensor p V) := sorry
