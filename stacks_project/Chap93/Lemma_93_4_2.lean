module

public import stacks_project.Chap90.Definition_90_16_8
public import stacks_project.Chap90.Lemma_90_16_4
public import stacks_project.Chap90.Lemma_90_16_11
public import stacks_project.Chap93.Example_93_4_1_Finite_projective_modules_Slice

/-!
# Rim-Schlessinger condition for finite projective modules

Example 93.4.1 satisfies (RS), so each residue-fibre slice `Def_V` is a deformation
category.
-/

@[expose] public section

open CategoryTheory Functor Limits
open scoped CategoricalPullback

noncomputable section

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat.FiniteProjective

/-- Lemma 93.4.2 (1): the category `F` of finite projective modules from Example 93.4.1
satisfies the Rim-Schlessinger condition (RS). -/
@[stacks 0DVP]
instance instHasRimSchlessinger : HasRimSchlessinger (groupoids Λ k).p := sorry

/-- Lemma 93.4.2 (2): in particular, `Def_V` is a deformation category for any
finite-dimensional vector space `V` over `k`. -/
@[stacks 0DVP]
instance instIsDeformationCategory_deformation
    (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    IsDeformationCategory
      (deformation V :
          CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
            (ArtinianLocalAlgCat Λ k)).p :=
  instIsDeformationCategory_overForget (groupoids Λ k).p (residueObject V)

/-- The fibre-category comparison of (90.10.1.1) for finite projective modules is an
equivalence along a given fibre-product square whose second leg is surjective. -/
theorem fiberComparison_isEquivalence (χ : (groupoids Λ k).p.op.Cleavage)
    {A A1 A2 P : ArtinianLocalAlgCat Λ k} (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (π1 : P ⟶ A1) (π2 : P ⟶ A2) (h : IsPullback π1 π2 f1 f2)
    (hf2 : Function.Surjective f2.hom) :
    (fiberComparison (groupoids Λ k).p χ h.w).IsEquivalence := sorry

end ArtinianLocalAlgCat.FiniteProjective
