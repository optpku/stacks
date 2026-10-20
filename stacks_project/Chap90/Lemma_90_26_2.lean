/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.KernelPair
import StacksCheckRecall

/-!
# Kernel-pair presentations of deformation functors

The kernel pair of a morphism from a deformation functor to a deformation category is
again a deformation functor, and its tangent space fits into an exact sequence
`0 ⟶ Inf(F) ⟶ T(R) ⟶ TU × TU`.
-/

@[expose] public section

open CategoryTheory Functor ArtinianLocalAlgCat

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {U : ArtinianLocalAlgCat Λ k ⥤ Type (max u v)}
variable {F : CofiberedCategoryOver.Groupoids.{u + 1, u, max (u + 1) (max u v), u}
    (ArtinianLocalAlgCat Λ k)}
variable (f : Functor.ofTypeValued U ⟶ F)
variable [IsDeformationCategory F.p] [IsDeformationFunctor U]

/- Lemma 90.26.2 (1): the kernel pair of a morphism from a deformation functor to a
 deformation category is a deformation functor. -/
@[stacks 06L6] #check
  (CategoryTheory.GroupoidInFunctors.instIsDeformationFunctor_relation f :
    IsDeformationFunctor (CategoryTheory.GroupoidInFunctors.relation f))

/- Lemma 90.26.2 (2): the canonical tangent sequence is exact, beginning with an
 injective map from the infinitesimal automorphisms of the deformation category. -/
@[stacks 06L6] #check
  (CategoryTheory.GroupoidInFunctors.infTangentSequence_exact f :
    Function.Injective (CategoryTheory.GroupoidInFunctors.connectingLinearMap f) ∧
      Function.Exact (CategoryTheory.GroupoidInFunctors.connectingLinearMap f)
        (CategoryTheory.GroupoidInFunctors.tangentProdLinearMap f))
