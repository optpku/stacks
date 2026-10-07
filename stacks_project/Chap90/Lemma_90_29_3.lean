module

public import stacks_project.Chap90.Lemma_90_29_3_Tensor
import StacksCheckRecall

/-!
# Lemma 90.29.3

In Situation 90.29.1, if `p` is a predeformation category whose associated
isomorphism-class functor satisfies (S2), there is a canonical bijective
`l`-linear comparison `T p ⊗[k] l ⟶ T(p_{l/k})` of tangent spaces.
-/

@[expose] public section

noncomputable section

open CategoryTheory hiding Linear
open CategoryTheory.Functor
open ArtinianLocalAlgCat
open scoped TensorProduct

universe u v w

variable (Λ k l : Type u) [CommRing Λ] [IsNoetherianRing Λ]
  [Field k] [Algebra Λ k] [Module.Finite Λ k]
  [Field l] [Algebra Λ l] [Module.Finite Λ l]
  [Algebra k l] [IsScalarTower Λ k l] [Module.Finite k l]
variable {F : Type v} [Category.{w} F] (p : F ⥤ ArtinianLocalAlgCat Λ k)
variable [IsPredeformationCategory p] [HasSchlessingerH2 (fiberIsoClassFunctor p)]

namespace ArtinianLocalAlgCat.residueChangeOver

/-- Lemma 90.29.3: With notation and assumptions as in Situation 90.29.1. Assume
`p` is a predeformation category and `fiberIsoClassFunctor p` satisfies (S2).
Then there is a canonical `l`-vector space isomorphism
`(fiberIsoClassFunctor p).obj (dualNumber Λ k) ⊗[k] l ⟶
(fiberIsoClassFunctor (residueChangeOver Λ k l p)).obj (dualNumber Λ l)` of
tangent spaces, given by `tangentSpaceTensor Λ k l p`. -/
@[stacks 07WB]
theorem bijective_tangentSpaceTensor :
    Function.Bijective (tangentSpaceTensor Λ k l p) :=
  sorry

end ArtinianLocalAlgCat.residueChangeOver
