/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap78.Lemma_78_21_1_QuotientMap
public import stacks_project.Chap78.Lemma_78_25_1_Restriction

/-!
# Full faithfulness of induced morphisms of quotient stacks

This file records the criterion that `[f] : [U/R] ⟶ [U'/R']` is fully faithful
if and only if the source groupoid is the restriction of the target along the
object map.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.Hom

/-- Lemma 78.25.1. Notation and assumption as in Lemma 78.21.1. The morphism of
quotient stacks `[f] : [U/R] ⟶ [U'/R']` is fully faithful if and only if `R`
is the restriction of `R'` via the morphism `f.obj : U ⟶ U'`. -/
@[stacks 046S]
theorem quotientStackMap_fullyFaithful_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) :
    Nonempty f.quotientStackMap.toFunctor.FullyFaithful ↔ IsRestriction f := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace.Hom
