/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced.Criteria
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 33.36.9: a scheme over a field of prime characteristic is geometrically reduced if and
only if its relative Frobenius target is reduced. -/
@[stacks 0CCE] #check
  (AlgebraicGeometry.SchemeOverField.geometricallyReduced_iff_isReduced_relativeFrobeniusTarget :
    ∀ {p : ℕ} [Fact p.Prime] {k : Type u} [Field k] [CharP k p]
      (X : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))),
      AlgebraicGeometry.SchemeOverField.geometricallyReduced X ↔
        AlgebraicGeometry.IsReduced
          (AlgebraicGeometry.Scheme.Hom.relativeFrobeniusTarget (p := p) X.hom))
