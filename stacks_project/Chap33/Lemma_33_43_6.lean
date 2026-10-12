/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Compactification

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 33.43.6: a reduced separated finite-type scheme over a field of topological Krull
dimension at most one has an H-projective compactification with finite closed boundary and
discrete valuation stalks at every boundary point. -/
@[stacks 0BXW] #check
  (AlgebraicGeometry.HProjective.exists_compactification_with_dvr_boundary_of_dimension_le_one :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [Scheme.Hom.FiniteType f] [IsSeparated f] [IsReduced X],
      topologicalKrullDim X ≤ 1 →
        ∃ (Xbar : Scheme.{u}) (fbar : Xbar ⟶ Spec (CommRingCat.of k)) (j : X ⟶ Xbar)
          (hj : IsOpenImmersion j),
          let U : Xbar.Opens := @Scheme.Hom.opensRange _ _ j hj
          j ≫ fbar = f ∧
            HProjective fbar ∧
            Dense (U : Set Xbar) ∧
            schemeTheoreticallyDense U ∧
            Set.Finite ((U : Set Xbar)ᶜ) ∧
            ∀ x ∈ ((U : Set Xbar)ᶜ),
              x ∈ closedPoints Xbar ∧
                ∃ (_ : IsDomain (Xbar.presheaf.stalk x)),
                  IsDiscreteValuationRing (Xbar.presheaf.stalk x))
