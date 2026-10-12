/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Variety

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

variable {p : ℕ} {k : Type u} [Field k] [Fact p.Prime] [CharP k p]
variable (X : SchemeOverField k) [Variety X]

/- Lemma 33.36.10: for a variety in positive characteristic, reducedness of its Frobenius
twist, geometric reducedness, and the existence of a nonempty smooth open are equivalent; the
relative Frobenius then has the stated variety, finiteness, dominance, and degree properties. -/
@[stacks 0CCF] #check
  (AlgebraicGeometry.SchemeOverField.relativeFrobenius_variety_tfae_and_properties
    (p := p) X :
    List.TFAE [
      IsReduced (Scheme.Hom.relativeFrobeniusTarget (p := p) X.hom),
      SchemeOverField.geometricallyReduced X,
      ∃ U : X.left.Opens, U ≠ ⊥ ∧ Smooth (U.ι ≫ X.hom)
    ] ∧
      ∀ hgeom : SchemeOverField.geometricallyReduced X,
        Variety (Scheme.Hom.relativeFrobeniusTargetOver (p := p) X.hom) ∧
          IsFinite (Scheme.Hom.relativeFrobenius (p := p) X.hom) ∧
          IsDominant (Scheme.Hom.relativeFrobenius (p := p) X.hom) ∧
          (
           -- Local instance justification (defeq pin): expose proved integrality of the canonical target.
           letI : IsIntegral (Scheme.Hom.relativeFrobeniusTarget (p := p) X.hom) :=
             (SchemeOverField.relativeFrobeniusTarget_variety_of_geometricallyReduced
               (p := p) X hgeom).toIsIntegral
           (Scheme.Hom.relativeFrobenius (p := p) X.hom).inducedFunctionFieldDegree =
             p ^ SchemeOverField.baseFieldTrdegAt X (genericPoint X.left)))
