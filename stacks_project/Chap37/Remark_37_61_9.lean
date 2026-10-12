/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Perfect.DualNumberCounterexample
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Remark 37.61.9: over a field, a morphism between schemes perfect over the base need not
be perfect; the residue-induced morphism from the point to its dual-number thickening is
the unique morphism over the base and gives a counterexample. -/
@[stacks 069A] #check
  (AlgebraicGeometry.DualNumber.perfectOverBase_and_reduction_not_perfect :
    ∀ (k : Type u) [Field k],
      AlgebraicGeometry.LocallyOfType RingHom.IsPerfectRingMap
          (𝟙 (AlgebraicGeometry.Spec (CommRingCat.of k))) ∧
        AlgebraicGeometry.LocallyOfType RingHom.IsPerfectRingMap
            (AlgebraicGeometry.Spec.map
              (CommRingCat.ofHom (algebraMap k (DualNumber k)))) ∧
          (∀ f : AlgebraicGeometry.Spec (CommRingCat.of k) ⟶
              AlgebraicGeometry.Spec (CommRingCat.of (DualNumber k)),
            f ≫ AlgebraicGeometry.Spec.map
                (CommRingCat.ofHom (algebraMap k (DualNumber k))) =
                𝟙 (AlgebraicGeometry.Spec (CommRingCat.of k)) ↔
              f = AlgebraicGeometry.Spec.map
                (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) ∧
          ¬ AlgebraicGeometry.LocallyOfType RingHom.IsPerfectRingMap
            (AlgebraicGeometry.Spec.map
              (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)))
