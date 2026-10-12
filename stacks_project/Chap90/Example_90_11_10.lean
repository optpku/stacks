/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Example_90_11_10_TangentSpace

/-!
# Tangent space of a predeformation functor on `C_Λ`

Definition 90.11.9 applies to a predeformation functor on
`ArtinianLocalAlgCat Λ k`, and the tangent space is `F(k[ε])`.
-/

@[expose] public section

open CategoryTheory

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor.IsPredeformationFunctor

/-- Example 90.11.10: since `ArtinianLocalAlgCat Λ k` contains `k[V]` for
finite-dimensional `k`-vector spaces `V`, Definition 90.11.9 applies with
`S = Λ`, `R = k`, `C = ArtinianLocalAlgCat Λ k`, and
`F : ArtinianLocalAlgCat Λ k ⥤ Type v` a predeformation functor. The tangent
space is `TF = F(k[ε])`. -/
@[stacks 06SR]
theorem tangentSpace_eq (F : ArtinianLocalAlgCat Λ k ⥤ Type v) [IsPredeformationFunctor F] :
    tangentSpace F = F.obj (ArtinianLocalAlgCat.dualNumber Λ k) := sorry

end CategoryTheory.Functor.IsPredeformationFunctor
