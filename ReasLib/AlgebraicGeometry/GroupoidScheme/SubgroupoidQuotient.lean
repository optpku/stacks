/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import ReasLib.AlgebraicGeometry.GroupoidScheme.AffineQuotient
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Morphism
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction

/-!
# Descent along a finite locally free subgroupoid quotient

A separated locally quasi-finite groupoid is the restriction of a groupoid on
the affine quotient by a finite locally free monic subgroupoid.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- A separated locally quasi-finite groupoid with affine objects descends along
the quotient by a finite locally free monic subgroupoid with the same objects. -/
theorem exists_isRestriction_objectQuotient {S : Scheme.{u}}
    (G P : GroupoidScheme S) (ι : Hom P G) (hU : P.U = G.U)
    (h_id : ι.IsIdentityOnObjects hU) [IsAffine P.U.left]
    [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [Mono ι.arrow.left] [Mono P.toPreRelation.hom.left]
    [IsSeparated G.toPreRelation.hom.left]
    [LocallyOfFiniteType G.toPreRelation.hom.left]
    [LocallyQuasiFinite G.toPreRelation.hom.left] :
    ∃ (Gbar : GroupoidScheme S) (hUbar : Gbar.U = objectQuotientOver P)
      (φ : Hom G (Gbar.pullback (quotientMapOf hU ≫ eqToHom hUbar.symm))),
      φ.IsIdentityOnObjects rfl ∧ IsIso φ.arrow := sorry

end AlgebraicGeometry.GroupoidScheme
