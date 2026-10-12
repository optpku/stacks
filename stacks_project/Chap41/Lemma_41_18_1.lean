/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.EtaleNeighborhood
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 41.18.1: Finitely many distinct points of one fibre at which a scheme morphism is
étale admit, after an étale base neighbourhood, finite families of open branches mapping
isomorphically to the neighbourhood, pairwise separated over its marked point, and covering all
lifted points above the chosen source points. -/
@[stacks 04HL] #check
  (AlgebraicGeometry.Scheme.Hom.exists_isIsoOpen_etaleNeighborhoods :
    {X S : Scheme.{u}} → (f : X ⟶ S) → (s : S) → (n : ℕ) → (x : Fin n → X) →
    (∀ i, f (x i) = s) → Function.Injective x → (∀ i, f.EtaleAt (x i)) →
    ∃ (U : EtaleNeighborhood S s) (m : Fin n → ℕ)
      (V : ∀ i, Fin (m i) → (pullback f U.toEtale.hom).Opens),
      let P := pullback f U.toEtale.hom
      let p := pullback.snd f U.toEtale.hom
      let q := pullback.fst f U.toEtale.hom
      let pV := fun i j ↦ (V i j).ι ≫ p
      ∃ (_ : ∀ i j, IsIso (pV i j))
        (_ : ∀ a b : Σ i, Fin (m i),
          U.point ∈ Set.range ((V a.1 a.2 ⊓ V b.1 b.2).ι ≫ p) → a = b),
        ∀ i (w : P), p w = U.point → q w = x i → ∃ j, w ∈ V i j)

end AlgebraicGeometry.Scheme.Hom
