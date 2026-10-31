/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation

/-!
# Relations on an algebraic space over a base

The canonical declarations for pre-relations, relations, and their pointwise
characterizations are owned by
`ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation`. This chapter module is
the source-facing import facade for Section 78.4; consumers use the generic
slice point API there, instantiating a scheme point with `Over.mk τ`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)]
  {B : AlgebraicSpace S} {U : Over B}

-- The source definition uses schemes over B; the owner also provides arbitrary slice points.
#check (PreRelation.pointRel : (P : PreRelation U) → (T : Over B) →
  (T ⟶ U) → (T ⟶ U) → Prop)
#check (PreRelation.isPreEquivalence_iff : ∀ (P : PreRelation U),
  P.IsPreEquivalence ↔ ∀ (T : Over S) (σ : ofOver T ⟶ B),
    Equivalence (P.pointRel (Over.mk σ)))
#check (PreRelation.isEquivalenceRelation_iff : ∀ (P : PreRelation U),
  IsEquivalenceRelation P.t P.s ↔ Mono P.hom ∧ P.IsPreEquivalence)
#check (PreRelation.isEquivalenceRelation_iff_schemePoints : ∀ (P : PreRelation U),
  IsEquivalenceRelation P.t P.s ↔ ∀ (T : Over S) (σ : ofOver T ⟶ B),
    Function.Injective (P.pointMap (Over.mk σ)) ∧ Equivalence (P.pointRel (Over.mk σ)))
#check (Relation.ofPreRelation : (P : PreRelation U) → [Mono P.hom] → Relation U)

end AlgebraicGeometry.AlgebraicSpace
