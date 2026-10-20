/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDegree.Etale

open AlgebraicGeometry
open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 29.57.8: for an étale morphism `f : X ⟶ Y` and a natural number `n`, the following
are equivalent: `n` bounds the degrees of the fibres of `f`; every field-valued base change
`Spec(k) ×[Y] X` has at most `n` points; and after base change to every separable algebraic
closure of every residue field `κ(y)`, the resulting fibre has at most `n` points. -/
@[stacks 03WU] #check
  (AlgebraicGeometry.Scheme.Hom.degreesOfFibresBoundedBy_tfae_card_le_of_etale :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] (n : ℕ),
      List.TFAE
        [ AlgebraicGeometry.Scheme.Hom.degreesOfFibresBoundedBy f n
        , ∀ (k : Type u) [Field k] (g : Spec (CommRingCat.of k) ⟶ Y),
            Finite (pullback f g : Scheme) ∧ Nat.card (pullback f g : Scheme) ≤ n
        , ∀ y : Y, ∀ (K : Type u) [Field K] [Algebra (Y.residueField y) K]
            [IsSepClosure (Y.residueField y) K],
            let g : Spec (CommRingCat.of K) ⟶ Y :=
              Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K)) ≫
                Y.fromSpecResidueField y
            Finite (pullback f g : Scheme) ∧ Nat.card (pullback f g : Scheme) ≤ n
        ])
