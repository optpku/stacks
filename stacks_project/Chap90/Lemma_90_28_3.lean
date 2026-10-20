/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalHomotopy.Versal
import StacksCheckRecall

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat CompleteLocalAlgCat Functor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

/- Lemma 90.28.3: if `p` is a deformation category over `ArtinianLocalAlgCat Λ k`
whose tangent space `(fiberIsoClassFunctor p).obj (dualNumber Λ k)` and infinitesimal
automorphism space `infinitesimalAutomorphisms p` are finite-dimensional over `k`, if
`ξ` is a versal formal object, and if `η` is a formal object, then any two maps
`f, g : ξ.base ⟶ η.base` such that there exist morphisms of formal objects
`a, b : ξ ⟶ η` with `a.base = f` and `b.base = g` (the project spelling of
`f_* ξ ≅ η ≅ g_* ξ`) are formally homotopic. -/
@[stacks 0DQD] #check (CompleteLocalAlgCat.FormallyHomotopic.of_isVersal :
  ∀ [Functor.IsDeformationCategory p]
    [FiniteDimensional k ((Functor.fiberIsoClassFunctor p).obj
      (ArtinianLocalAlgCat.dualNumber Λ k))]
    [FiniteDimensional k (Functor.infinitesimalAutomorphisms p)]
    (ξ : FormalObject p) [FormalObject.IsVersal ξ]
    (η : FormalObject p) {f g : ξ.base ⟶ η.base},
    (∃ a : ξ ⟶ η, a.base = f) → (∃ b : ξ ⟶ η, b.base = g) →
      FormallyHomotopic f g)

/- Morphisms of formal objects from a versal formal object to a common target have
formally homotopic complete local bases. -/
#check (CompleteLocalAlgCat.FormallyHomotopic.of_isVersal_hom :
  ∀ [Functor.IsDeformationCategory p]
    [FiniteDimensional k ((Functor.fiberIsoClassFunctor p).obj
      (ArtinianLocalAlgCat.dualNumber Λ k))]
    [FiniteDimensional k (Functor.infinitesimalAutomorphisms p)]
    (ξ : FormalObject p) [FormalObject.IsVersal ξ]
    (η : FormalObject p) (a b : ξ ⟶ η),
    FormallyHomotopic a.base b.base)
