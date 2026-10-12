/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import stacks_project.Chap90.Definition_90_16_8
public import stacks_project.Chap90.Definition_90_27_1_MinimalVersal
public import stacks_project.Chap90.Lemma_90_20_1_LinearMap
public import stacks_project.Chap90.Lemma_90_28_2_FormalHomotopy

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat CompleteLocalAlgCat Functor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}
variable [IsDeformationCategory p]
variable [FiniteDimensional k ((fiberIsoClassFunctor p).obj (dualNumber Λ k))]
variable [FiniteDimensional k (infinitesimalAutomorphisms p)]

namespace CompleteLocalAlgCat

/-- Lemma 90.28.3: if `p` is a deformation category over `ArtinianLocalAlgCat Λ k`
whose tangent space `(fiberIsoClassFunctor p).obj (dualNumber Λ k)` and infinitesimal
automorphism space `infinitesimalAutomorphisms p` are finite-dimensional over `k`, if
`ξ` is a versal formal object, and if `η` is a formal object, then any two maps
`f, g : ξ.base ⟶ η.base` such that there exist morphisms of formal objects
`a, b : ξ ⟶ η` with `a.base = f` and `b.base = g` (the project spelling of
`f_* ξ ≅ η ≅ g_* ξ`) are formally homotopic. -/
@[stacks 0DQD]
theorem FormallyHomotopic.of_isVersal (ξ : FormalObject p) [FormalObject.IsVersal ξ]
    (η : FormalObject p) {f g : ξ.base ⟶ η.base}
    (hf : ∃ a : ξ ⟶ η, a.base = f) (hg : ∃ b : ξ ⟶ η, b.base = g) :
    FormallyHomotopic f g := sorry

/-- Morphisms of formal objects from a versal formal object to a common target have
formally homotopic complete local bases. -/
theorem FormallyHomotopic.of_isVersal_hom (ξ : FormalObject p) [FormalObject.IsVersal ξ]
    (η : FormalObject p) (a b : ξ ⟶ η) :
    FormallyHomotopic a.base b.base := sorry

end CompleteLocalAlgCat
