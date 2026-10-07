module

public import ReasLib.CategoryTheory.Fibered.CategoryHomology.AdjointFactorization.LeftDerived
import StacksCheckRecall

@[expose] public section

/-!
# Comparison-index homology for a morphism of fibered categories

The reusable construction is owned by the `AdjointFactorization` leaves in `ReasLib`.  This file
keeps the Chapter 21 source statement as a compact recall surface and distinguishes the universal
comparison from its projective computational model.
-/

open CategoryTheory

/- Lemma 21.40.3 (08PK): in Situation `21.38.3`, for an abelian sheaf `𝓕'` on `𝒞'` and `n ≥ 0`,
the `n`-th left derived lower shriek `L_n g_!(𝓕')` is canonically isomorphic to the sheaf attached
to `U ↦ H_n(𝓘_U, 𝓕'_U)`, where `𝓘_U` is the comparison indexing category. -/
@[stacks 08PK "comparison-index universal lower-shriek homology"]
#check @FiberedCategoryOver.FiberHomology.AdjointFactorization.universal_obj_isomorphic

@[stacks 08PK "comparison-index degree-zero lower-shriek comparison"]
#check @FiberedCategoryOver.FiberHomology.AdjointFactorization.lowerShriek_isomorphic_deltaFunctor_zero

@[stacks 08PK "comparison-index homology sheaf object formula"]
#check @FiberedCategoryOver.FiberHomology.AdjointFactorization.sheafOfSheaf

@[stacks 08PK "projective comparison-index lower-shriek computation"]
#check @FiberedCategoryOver.FiberHomology.AdjointFactorization.leftDerived_obj_isomorphic

@[stacks 08PK "comparison-index homology delta-functor owner"]
#check @FiberedCategoryOver.FiberHomology.AdjointFactorization.deltaFunctor
