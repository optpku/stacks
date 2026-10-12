/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CohenMacaulay.AffineSpace

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 37.22.8: for a flat, locally finitely presented scheme morphism, being
Cohen--Macaulay at a point is equivalent to the existence and universal flatness
criteria for quasi-finite maps from neighborhoods into relative affine space of
the fiber dimension. -/
@[stacks 0BUU]
#check
  (AlgebraicGeometry.Scheme.Hom.cohenMacaulayAt_tfae_affineSpace :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
      (x : X) (d : ℕ) (hfdim : f.fiberDimensionAt x = (d : WithBot ℕ∞)),
      let A := AffineSpace (ULift.{u} (Fin d)) S
      List.TFAE [
        f.CohenMacaulayAt x,
        ∃ (U : X.Opens) (hxU : x ∈ U) (g : U.toScheme ⟶ A),
          g ≫ (A ↘ S) = U.ι ≫ f ∧
            LocallyOfFiniteType g ∧ LocallyQuasiFinite g ∧ g.flatAt ⟨x, hxU⟩,
        ∃ (U : X.Opens) (hxU : x ∈ U) (g : U.toScheme ⟶ A),
          g ≫ (A ↘ S) = U.ι ≫ f ∧
            LocallyOfFiniteType g ∧ LocallyQuasiFinite g ∧ Flat g,
        ∀ (U : X.Opens) (hxU : x ∈ U) (g : U.toScheme ⟶ A),
          g ≫ (A ↘ S) = U.ι ≫ f →
            AlgebraicGeometry.Scheme.Hom.FiniteType.QuasiFiniteAt g ⟨x, hxU⟩ →
              g.flatAt ⟨x, hxU⟩
      ])
