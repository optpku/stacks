/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.Hull
import StacksCheckRecall

/-!
# Hull of isomorphism classes of ring deformations

In Example 93.8.1, if `P` is a finite type `k`-algebra whose spectrum is smooth
over `k` except at finitely many points, and `Λ` is classical, then the functor
of isomorphism classes of objects of `Def_P` has a hull.
-/

@[expose] public section

open Algebra CategoryTheory Functor

noncomputable section

universe u

namespace FlatAlgebraCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Lemma 93.8.6
In Example 93.8.1 assume `P` is a finite type `k`-algebra such that
`Spec(P) ⟶ Spec(k)` is smooth except at a finite number of points, recorded as
`(smoothLocus k P)ᶜ.Finite`. Assume `Λ` is a complete local ring with residue
field `k` (the classical case `ArtinianLocalAlgCat.IsClassical Λ k`). Then the
functor `F` sending `A` to the isomorphism classes of objects of `Def_P(A)`,
i.e. `(fiberIsoClassFunctor (deformationForget Λ k P)).obj A`, has a hull.
Equivalently, there exists a hull of the associated cofibered set
`isoClassProjection (deformationForgetULift Λ k P)`. -/
@[stacks 0ET4] #check (FlatAlgebraCat.exists_isHull_isoClass Λ k :
  ∀ (P : Type u) [CommRing P] [Algebra k P]
    [Algebra.FiniteType k P] [ArtinianLocalAlgCat.IsClassical Λ k],
    (smoothLocus k P)ᶜ.Finite →
    ∃ ξ : FormalObject
      (isoClassProjection (FlatAlgebraCat.deformationForgetULift Λ k P)),
      FormalObject.IsHull ξ)

end FlatAlgebraCat
