/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Compactification
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Lemma 33.43.5: A separated finite-type scheme over a field of topological Krull dimension at
most one admits an H-projective compactification with dense and scheme-theoretically dense image
and finite closed-point boundary. -/
@[stacks 0BXV] #check
  (AlgebraicGeometry.HProjective.exists_compactification_of_dimension_le_one :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
      [Scheme.Hom.FiniteType f] [IsSeparated f] (hdim : topologicalKrullDim X ≤ 1),
    ∃ (Xbar : Scheme.{u}) (fbar : Xbar ⟶ Spec (CommRingCat.of k)) (j : X ⟶ Xbar)
      (hj : IsOpenImmersion j),
      let U : Xbar.Opens := @Scheme.Hom.opensRange _ _ j hj
      j ≫ fbar = f ∧
        HProjective fbar ∧
        Dense (U : Set Xbar) ∧
        schemeTheoreticallyDense U ∧
        Set.Finite ((U : Set Xbar)ᶜ) ∧
        ∀ x ∈ ((U : Set Xbar)ᶜ), x ∈ closedPoints Xbar)

end AlgebraicGeometry
