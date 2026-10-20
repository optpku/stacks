/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidScheme.AffineQuotient
public import ReasLib.AlgebraicGeometry.GroupoidScheme.SubgroupoidQuotient

/-!
# Quotient by a finite locally free subgroupoid

If `(U, R, s, t, c)` is a groupoid scheme over `S` and `P → R` is a monomorphism
making `(U, P, s|_P, t|_P, c|_P)` a groupoid with finite locally free source and
target, monic `j|_P`, affine `U`, and separated locally quasi-finite `j`, then
the fppf quotient `U / P` is an affine scheme and `R` is the restriction of a
groupoid on that quotient.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/- Lemma 80.9.1 (1): the invariant spectrum represents the affine fppf quotient. -/
@[stacks 04S4] #check (AlgebraicGeometry.GroupoidScheme.objectQuotient_represents :
  ∀ {S : Scheme.{u}} (P : GroupoidScheme S),
    [IsAffine P.U.left] → [IsFiniteLocallyFree P.s.left] →
    [IsFiniteLocallyFree P.t.left] → [Mono P.toPreRelation.hom.left] →
    IsAffine (objectQuotient P) ∧ IsIso (objectQuotientSheafComparison P))

/- Lemma 80.9.1 (2): the quotient morphism is finite locally free. -/
@[stacks 04S4] #check (AlgebraicGeometry.GroupoidScheme.quotientMapOf_isFiniteLocallyFree :
  ∀ {S : Scheme.{u}} {G P : GroupoidScheme S} (hU : P.U = G.U),
    [IsAffine P.U.left] → [IsFiniteLocallyFree P.s.left] →
    [IsFiniteLocallyFree P.t.left] → [Mono P.toPreRelation.hom.left] →
    IsFiniteLocallyFree (quotientMapOf hU).left)

/- Lemma 80.9.1 (3): the canonical `(t, s)` comparison identifies the subgroupoid
with the kernel pair of the quotient morphism. -/
@[stacks 04S4] #check (AlgebraicGeometry.GroupoidScheme.objectQuotient_kernelPair_isIso :
  ∀ {S : Scheme.{u}} (P : GroupoidScheme S),
    [IsAffine P.U.left] → [IsFiniteLocallyFree P.s.left] →
    [IsFiniteLocallyFree P.t.left] → [Mono P.toPreRelation.hom.left] →
    IsIso (P.toPreRelation.kernelPairLift (objectQuotientMap P)
      (objectQuotientMap_equalizes P)))

/- Lemma 80.9.1 (4): the ambient groupoid is the restriction of a groupoid on
the affine quotient along the quotient morphism. -/
@[stacks 04S4] #check (AlgebraicGeometry.GroupoidScheme.exists_isRestriction_objectQuotient :
  ∀ {S : Scheme.{u}} (G P : GroupoidScheme S) (ι : Hom P G) (hU : P.U = G.U)
    (h_id : ι.IsIdentityOnObjects hU), [IsAffine P.U.left] →
    [IsFiniteLocallyFree P.s.left] → [IsFiniteLocallyFree P.t.left] →
    [Mono ι.arrow.left] → [Mono P.toPreRelation.hom.left] →
    [IsSeparated G.toPreRelation.hom.left] →
    [LocallyOfFiniteType G.toPreRelation.hom.left] →
    [LocallyQuasiFinite G.toPreRelation.hom.left] →
    ∃ (Gbar : GroupoidScheme S) (hUbar : Gbar.U = objectQuotientOver P)
      (φ : Hom G (Gbar.pullback (quotientMapOf hU ≫ eqToHom hUbar.symm))),
      φ.IsIdentityOnObjects rfl ∧ IsIso φ.arrow)

end AlgebraicGeometry.GroupoidScheme
