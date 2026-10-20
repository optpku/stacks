/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidsOver.ArtinApproximation.Existence

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing
open AlgebraicGeometry.Groupoids.Hom
open AlgebraicGeometry.GroupoidsOver
open FiberedCategoryOver.Groupoids

universe u

/- Lemma 98.10.1: let `S` be a locally Noetherian scheme, let `X` be a category
fibred in groupoids over `(Sch/S)_fppf`, and let `x` be an object of `X` lying
over `Spec(R)` for a Noetherian complete local ring `R` with residue field `k`
of finite type over `S`. Let `s` be the image of `Spec(k) ⟶ S`. Assume
`S.presheaf.stalk s` is a G-ring and the structure morphism of `X` is limit
preserving on objects. Then for every `N ≥ 1` there exist a finite type
`S`-algebra `A`, a maximal ideal `m_A ⊂ A`, an object of `X` over `Spec(A)`,
an `S`-isomorphism `R ⧸ m_R ^ N ≃+* A ⧸ m_A ^ N`, an isomorphism of the
restrictions of `x` and that object to those `N`-truncations lying over the
`S`-isomorphism, and an isomorphism of associated graded `k`-algebras. -/
@[stacks 07XB] #check
  (AlgebraicGeometry.GroupoidsOver.ArtinApproximation.nonempty_of_isGRing :
    ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
    (X : GroupoidsOver S)
    [LimitPreservingOnObjects (baseProjection.{u + 1, u, u + 1} X)]
    (x : CompleteLocalObject X) (s : S)
    (hs : x.base.toS (closedPoint x.base.carrier) = s)
    [IsGRing (S.presheaf.stalk s)] (N : ℕ) (hN : 1 ≤ N),
    Nonempty (ArtinApproximation x N))
