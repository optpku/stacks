/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Purity
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
/- Lemma 58.28.3 (Purity of ramification locus) -/
@[stacks 0EA4] #check
  (AlgebraicGeometry.Scheme.Hom.etaleAt_of_etaleAt_codimOne_specializations :
    ∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y),
      [IsLocallyNoetherian X] → [IsLocallyNoetherian Y] → [LocallyOfFiniteType f] →
      (x : X) → X.isNormalAt x →
      IsRegularLocalRing (Y.presheaf.stalk (f.base x)) →
      1 ≤ ringKrullDim (X.presheaf.stalk x) →
      (∀ x' : X, x' ⤳ x → ringKrullDim (X.presheaf.stalk x') = 1 → f.EtaleAt x') →
      f.EtaleAt x)
