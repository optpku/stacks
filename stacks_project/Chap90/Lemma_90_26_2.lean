/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Lemma_90_26_2_Instances
public import stacks_project.Chap90.Lemma_90_26_2_LinearMap
import Mathlib.Tactic.CrossRefAttribute

/-!
# Kernel-pair presentations of deformation functors

The kernel pair of a morphism from a deformation functor to a deformation category is
again a deformation functor, and its tangent space fits into an exact sequence
`0 ⟶ Inf(F) ⟶ T(R) ⟶ TU × TU`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Functor ArtinianLocalAlgCat

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {U : ArtinianLocalAlgCat Λ k ⥤ Type (max u v)}
variable {F : CofiberedCategoryOver.Groupoids.{u + 1, u, max (u + 1) (max u v), u}
    (ArtinianLocalAlgCat Λ k)}

namespace CategoryTheory.GroupoidInFunctors

/-- Lemma 90.26.2 (1): if `F` is a deformation category, `U` is a deformation functor, and
`f : U ⟶ F` is a morphism of categories cofibered in groupoids, then the kernel-pair functor
`relation f` (that is, `U ×_{f, F, f} U`) is a deformation functor. -/
@[stacks 06L6]
instance instIsDeformationFunctor_relation (f : Functor.ofTypeValued U ⟶ F)
    [IsDeformationCategory F.p] [IsDeformationFunctor U] :
    IsDeformationFunctor (relation f) := sorry

/-- Lemma 90.26.2 (2): if `F` is a deformation category, `U` is a deformation functor, and
`f : U ⟶ F` is a morphism of categories cofibered in groupoids, then the tangent space of
`relation f` fits into an exact sequence of `k`-vector spaces
`0 ⟶ Inf(F) ⟶ T(relation f) ⟶ TU × TU`, where the maps are `connectingLinearMap` and
`tangentProdLinearMap`. -/
@[stacks 06L6]
theorem infTangentSequence_exact (f : Functor.ofTypeValued U ⟶ F)
    [IsDeformationCategory F.p] [IsDeformationFunctor U] :
    Function.Injective (connectingLinearMap f) ∧
      Function.Exact (connectingLinearMap f) (tangentProdLinearMap f) := sorry

end CategoryTheory.GroupoidInFunctors
