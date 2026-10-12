/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.InfinitesimalNeighbourhood.UniversalProperty
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.5.2 (1): every first-order thickening over the ambient scheme uniquely factors
through the first-order infinitesimal neighbourhood of an immersion. -/
@[stacks 04EZ] #check
  (AlgebraicGeometry.Scheme.Hom.InfinitesimalNeighbourhood.existsUnique_lift_firstOrder :
    {Z X T T' : AlgebraicGeometry.Scheme.{u}} →
      (i : Z ⟶ X) → [AlgebraicGeometry.IsImmersion i] →
      (j : T ⟶ T') → [AlgebraicGeometry.IsFirstOrderThickening j] →
      (a : T ⟶ Z) → (b : T' ⟶ X) → (sq : CommSq a j i b) →
      Nonempty (Unique
        (AlgebraicGeometry.Scheme.Hom.InfinitesimalNeighbourhood.factorizationCommSq
          i 1 j a b sq).LiftStruct))

/- Lemma 37.5.2 (2): for `1 ≤ n`, every `n`th-order thickening over the ambient scheme
uniquely factors through the `n`th infinitesimal neighbourhood of an immersion. -/
@[stacks 04EZ] #check
  (AlgebraicGeometry.Scheme.Hom.InfinitesimalNeighbourhood.existsUnique_lift :
    {Z X T T' : AlgebraicGeometry.Scheme.{u}} →
      (i : Z ⟶ X) → [AlgebraicGeometry.IsImmersion i] →
      (n : ℕ) → 1 ≤ n →
      (j : T ⟶ T') → [AlgebraicGeometry.IsNthOrderThickening n j] →
      (a : T ⟶ Z) → (b : T' ⟶ X) → (sq : CommSq a j i b) →
      Nonempty (Unique
        (AlgebraicGeometry.Scheme.Hom.InfinitesimalNeighbourhood.factorizationCommSq
          i n j a b sq).LiftStruct))
