module

public import stacks_project.Chap90.Lemma_90_29_4_Tensor
import StacksCheckRecall

/-!
# Lemma 90.29.4

In Situation 90.29.1, if `p` is a deformation category, there is a canonical
bijective `l`-linear comparison `Inf(p) ⊗[k] l ⟶ Inf(p_{l/k})` of infinitesimal
automorphism spaces.
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
variable [IsDeformationCategory p]

namespace ArtinianLocalAlgCat.residueChangeOver

/-- Lemma 90.29.4: With notation and assumptions as in Situation 90.29.1. Assume
`p` is a deformation category. Then there is a canonical `l`-vector space isomorphism
`infinitesimalAutomorphismsAt p (chosenResidueFiberObj p)
  (Chosen.pushforwardObj p (residueToDualNumber Λ k) (chosenResidueFiberObj p))
  (chosenDualNumberHom p (chosenResidueFiberObj p)) ⊗[k] l ⟶
infinitesimalAutomorphismsAt (residueChangeOver Λ k l p)
  (chosenResidueFiberObj (residueChangeOver Λ k l p))
  (Chosen.pushforwardObj (residueChangeOver Λ k l p) (residueToDualNumber Λ l)
    (chosenResidueFiberObj (residueChangeOver Λ k l p)))
  (chosenDualNumberHom (residueChangeOver Λ k l p)
    (chosenResidueFiberObj (residueChangeOver Λ k l p)))`
of infinitesimal automorphism spaces, given by `infAutTensor Λ k l p`. -/
@[stacks 07WC]
theorem bijective_infAutTensor :
    Function.Bijective (infAutTensor Λ k l p) :=
  sorry

end ArtinianLocalAlgCat.residueChangeOver
