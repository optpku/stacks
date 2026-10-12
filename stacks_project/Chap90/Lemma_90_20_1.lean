/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Lemma_90_20_1_Instances
public import stacks_project.Chap90.Lemma_90_20_1_LinearMap

/-!
# 2-fibre products of deformation categories

The 2-fibre product of deformation categories is a deformation category, and the
six-term sequence of infinitesimal automorphism groups and tangent spaces is exact.
-/

@[expose] public section

noncomputable section

open CategoryTheory Functor CofiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

/-- Lemma 90.20.1 (1): if `f : H ⟶ F` and `g : G ⟶ F` are 1-morphisms of deformation
categories, then the 2-fibre product `W = TwoFibreProduct.apex f g` is a deformation
category. -/
@[stacks 06L5]
instance instIsDeformationCategory_twoFibreProduct
    {F G H : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (ArtinianLocalAlgCat Λ k)}
    (f : H ⟶ F) (g : G ⟶ F)
    [IsDeformationCategory F.p] [IsDeformationCategory G.p] [IsDeformationCategory H.p] :
    IsDeformationCategory (p (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)) := sorry

end CategoryTheory.Functor

namespace CategoryTheory.BasedFunctor

/-- Lemma 90.20.1 (2): if `f : H ⟶ F` and `g : G ⟶ F` are 1-morphisms of deformation
categories and `W = TwoFibreProduct.apex f g`, then the sequence of `k`-vector spaces
`0 ⟶ Inf(W) ⟶ Inf(H) × Inf(G) ⟶ Inf(F) ⟶ T W ⟶ T H × T G ⟶ T F` is exact, where the
maps are `infProdLinearMap`, `infDiffLinearMap` (the coproduct difference `Inf(f) - Inf(g)`),
`connectingLinearMap`, `tangentProdLinearMap`, and `tangentDiffLinearMap` (the coproduct
difference `df - dg`). Source `⊕` is the module product `×`. -/
@[stacks 06L5]
theorem infTangentSequence_exact
    {F G H : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (ArtinianLocalAlgCat Λ k)}
    (f : H ⟶ F) (g : G ⟶ F)
    [IsDeformationCategory F.p] [IsDeformationCategory G.p] [IsDeformationCategory H.p] :
    Function.Injective (infProdLinearMap f g) ∧
      Function.Exact (infProdLinearMap f g) (infDiffLinearMap f g) ∧
      Function.Exact (infDiffLinearMap f g) (connectingLinearMap f g) ∧
      Function.Exact (connectingLinearMap f g) (tangentProdLinearMap f g) ∧
      Function.Exact (tangentProdLinearMap f g) (tangentDiffLinearMap f g) := sorry

end CategoryTheory.BasedFunctor
