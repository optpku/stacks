module

public import stacks_project.Chap90.Remark_90_6_3_PredeformationFunctor
public import stacks_project.Chap90.Definition_90_10_1_DualNumber

/-!
# Tangent space of a predeformation functor

The tangent space `TF` of a predeformation functor
`F : ArtinianLocalAlgCat Λ k ⥤ Type v` is the value
`F.obj (ArtinianLocalAlgCat.dualNumber Λ k)`.
-/

@[expose] public section

open CategoryTheory

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor.IsPredeformationFunctor

/-- The tangent space of a predeformation functor is its value at the dual-number
object `k[ε]` of `ArtinianLocalAlgCat Λ k`. -/
def tangentSpace (F : ArtinianLocalAlgCat Λ k ⥤ Type v) [IsPredeformationFunctor F] : Type v :=
  F.obj (ArtinianLocalAlgCat.dualNumber Λ k)

/-- The tangent space of a predeformation functor is `F` evaluated at
`ArtinianLocalAlgCat.dualNumber Λ k`. -/
theorem tangentSpace_def (F : ArtinianLocalAlgCat Λ k ⥤ Type v) [IsPredeformationFunctor F] :
    tangentSpace F = F.obj (ArtinianLocalAlgCat.dualNumber Λ k) := sorry

end CategoryTheory.Functor.IsPredeformationFunctor
