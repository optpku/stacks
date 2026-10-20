/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.EtaleNeighborhood
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 41.17.1: Finitely many distinct points of one fibre where a scheme morphism is
unramified admit, after an étale base neighbourhood, finite families of open pieces mapping to
the neighbourhood as closed immersions through its marked point, pairwise separated over that
point, and covering all lifted points above the chosen source points. -/
@[stacks 04HH]
#check (AlgebraicGeometry.Scheme.Hom.exists_closedImmersionOpen_etaleNeighborhoods :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (s : S) (n : ℕ) (x : Fin n → X),
    (∀ i, f (x i) = s) → Function.Injective x → (∀ i, f.UnramifiedAt (x i)) →
      ∃ (U : EtaleNeighborhood S s) (m : Fin n → ℕ)
        (V : ∀ i, Fin (m i) → (pullback f U.toEtale.hom).Opens),
        let P := pullback f U.toEtale.hom
        let p := pullback.snd f U.toEtale.hom
        let q := pullback.fst f U.toEtale.hom
        let pV := fun i j ↦ (V i j).ι ≫ p
        ∃ (h_closed : ∀ i j, IsClosedImmersion (pV i j))
          (h_through : ∀ i j, U.point ∈ Set.range (pV i j))
          (h_separate : ∀ a b : Σ i, Fin (m i),
            U.point ∈ Set.range ((V a.1 a.2 ⊓ V b.1 b.2).ι ≫ p) → a = b),
          ∀ i (w : P), p w = U.point → q w = x i → ∃ j, w ∈ V i j)

end AlgebraicGeometry.Scheme.Hom
