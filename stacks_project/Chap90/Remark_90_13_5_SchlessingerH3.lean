module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import stacks_project.Chap90.Example_90_11_10_TangentSpace
public import stacks_project.Chap90.Remark_90_6_3_PredeformationFunctor

/-!
# Schlessinger's condition (H3)

For a predeformation functor `F : ArtinianLocalAlgCat Λ k ⥤ Type v`,
Schlessinger's condition (H3) is finite-dimensionality of the tangent space
`IsPredeformationFunctor.tangentSpace F` over `k`.
-/

@[expose] public section

open CategoryTheory

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

/-- Schlessinger's condition (H3): the tangent space of a predeformation functor is
finite-dimensional over `k`. -/
abbrev HasSchlessingerH3 (F : ArtinianLocalAlgCat Λ k ⥤ Type v)
    [IsPredeformationFunctor F]
    [AddCommGroup (IsPredeformationFunctor.tangentSpace F)]
    [Module k (IsPredeformationFunctor.tangentSpace F)] : Prop :=
  FiniteDimensional k (IsPredeformationFunctor.tangentSpace F)

/-- Schlessinger's (H3) is finite-dimensionality of `IsPredeformationFunctor.tangentSpace F`. -/
theorem hasSchlessingerH3_iff (F : ArtinianLocalAlgCat Λ k ⥤ Type v)
    [IsPredeformationFunctor F]
    [AddCommGroup (IsPredeformationFunctor.tangentSpace F)]
    [Module k (IsPredeformationFunctor.tangentSpace F)] :
    HasSchlessingerH3 F ↔
      FiniteDimensional k (IsPredeformationFunctor.tangentSpace F) := sorry

end CategoryTheory.Functor
