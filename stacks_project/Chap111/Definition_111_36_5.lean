/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Noetherian.Characterization
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

variable (X : Scheme.{u}) (R : CommRingCat.{u})

/- Definition 111.36.5 (1): a scheme is locally Noetherian if and only if every point has
an affine open neighbourhood whose coordinate ring is Noetherian. -/
@[stacks 029S]
#check (AlgebraicGeometry.isLocallyNoetherian_iff_affineOpen_neighborhoods X :
  AlgebraicGeometry.IsLocallyNoetherian X ↔ ∀ point : X, ∃ neighborhood : X.affineOpens,
    point ∈ (neighborhood : X.Opens) ∧ IsNoetherianRing Γ(X, neighborhood))

#check (AlgebraicGeometry.IsLocallyNoetherian X : Prop)

/- Companion check: for an affine scheme `Spec R`, local Noetherianity is equivalent to the
ring `R` being Noetherian. -/
#check (AlgebraicGeometry.isLocallyNoetherian_Spec :
  AlgebraicGeometry.IsLocallyNoetherian (Spec R) ↔ IsNoetherianRing R)

/- Definition 111.36.5 (2): a scheme is Noetherian if it is locally Noetherian and
quasi-compact, equivalently compact with Noetherian section rings on every affine open. -/
@[stacks 029S]
#check (AlgebraicGeometry.isNoetherian_iff_compactSpace_and_affineSections X :
  AlgebraicGeometry.IsNoetherian X ↔ CompactSpace X ∧
    ∀ neighborhood : X.affineOpens, IsNoetherianRing Γ(X, neighborhood))

#check (AlgebraicGeometry.IsNoetherian X : Prop)

/- Companion check: the canonical scheme-level characterization of Noetherian schemes is local
Noetherianity together with quasi-compactness. -/
#check (AlgebraicGeometry.isNoetherian_iff X :
  AlgebraicGeometry.IsNoetherian X ↔ AlgebraicGeometry.IsLocallyNoetherian X ∧ CompactSpace X)
