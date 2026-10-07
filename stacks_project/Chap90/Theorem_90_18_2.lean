module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import stacks_project.Chap90.Definition_90_6_1_Prorepresentable
public import stacks_project.Chap90.Lemma_90_26_2_Instances
public import stacks_project.Chap90.Lemma_90_26_2_LinearMap
public import stacks_project.Chap90.Remark_90_16_9_DeformationFunctor
public import stacks_project.Chap90.Theorem_90_18_2_OfDerivation

/-!
# Schlessinger's theorem on prorepresentable functors

A functor `F : ArtinianLocalAlgCat Λ k ⥤ Type u` is prorepresentable if and only
if it is a deformation functor, its tangent space is finite-dimensional over `k`,
and the canonical map `ofDerivation F` is injective.
-/

@[expose] public section

open CategoryTheory
open Functor.IsPredeformationFunctor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

/-- Theorem 90.18.2: a functor `F : ArtinianLocalAlgCat Λ k ⥤ Type u` is
prorepresentable if and only if (a) `F` is a deformation functor, (b)
`FiniteDimensional k (tangentSpace F)`, and (c) `ofDerivation F` is injective. -/
@[stacks 06JM]
theorem isProrepresentable_iff_finiteDimensional_ofDerivation
    {F : ArtinianLocalAlgCat Λ k ⥤ Type u}
    [IsPredeformationFunctor F] [HasSchlessingerH2 F] :
    IsProrepresentable F ↔
      IsDeformationFunctor F ∧
        FiniteDimensional k (tangentSpace F) ∧
        Function.Injective (ofDerivation F) := sorry

end CategoryTheory.Functor
