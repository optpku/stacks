/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Etale.Essential
public import ReasLib.RingTheory.Etale.Neighborhood.GeometricallyUnibranch

/-!
# Essentially etale maps from geometrically unibranch local domains

This leaf owns the local criterion turning an injective, essentially finite
type local map from a geometrically unibranch local domain into an essentially
etale map.
@stack 0GS6
-/

@[expose] public section

open IsLocalRing

universe u v

namespace Algebra.EssEtale

variable {A : Type u} {B : Type v}
variable [CommRing A] [IsDomain A] [IsLocalRing A]
variable [IsGeometricallyUnibranch A]
variable [CommRing B] [IsLocalRing B] [Algebra A B]
variable [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B]

/-- Lemma 15.108.3: an injective essentially finite type local map from a
geometrically unibranch local domain is essentially etale when the source
maximal ideal extends to the target maximal ideal and the residue-field
extension is separable.  This repository keeps the historical snapshot
numbering; the current Stacks page is 15.109.3 with tag `0GS6`.

Proof strategy: use `Algebra.EssFiniteType.subalgebra A B` as the finite type
model, transfer the closed-point hypotheses to its prime below `closedPoint B`,
apply the etale-neighborhood theorem there, and retain the original
localization presentation of `B`.  Applying the neighborhood theorem directly
to the local ring `B` would incorrectly force `B` itself to be finitely
presented over `A`. -/
@[stacks 0GS6 "Lemma 15.108.3"]
theorem of_geometricallyUnibranch_of_injective
    (h_injective : Function.Injective (algebraMap A B))
    (h_maximal : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B)
    (h_separable : Algebra.IsSeparable (ResidueField A) (ResidueField B)) :
    Algebra.EssEtale A B := sorry
-- Proof strategy: pass to `Algebra.EssFiniteType.subalgebra A B`, transfer the closed-point
-- hypotheses, apply the geometrically-unibranch etale-neighborhood theorem, and reuse the
-- localization presentation of `B`.

end Algebra.EssEtale
