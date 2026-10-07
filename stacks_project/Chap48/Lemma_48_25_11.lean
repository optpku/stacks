module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Gorenstein.AffineSpace

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

/- Lemma 48.25.11 (1): for a flat, locally finitely presented morphism, being
Gorenstein at a point is equivalent to the three relative-affine-space
criteria involving locally quasi-finite maps. -/
@[stacks 0C09] #check
  (AlgebraicGeometry.Scheme.Hom.gorensteinAt_tfae_affineSpace :
    ∀ {X S : Scheme} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
      (x : X) (d : ℕ), f.fiberDimensionAt x = (d : WithBot ℕ∞) →
      let A := AffineSpace (ULift (Fin d)) S
      List.TFAE [
        f.gorensteinAt x,
        ∃ (U : X.Opens) (hxU : x ∈ U) (g : U.toScheme ⟶ A),
          g ≫ (A ↘ S) = U.ι ≫ f ∧
            LocallyOfFiniteType g ∧ LocallyQuasiFinite g ∧
              g.gorensteinAt ⟨x, hxU⟩,
        ∃ (U : X.Opens) (hxU : x ∈ U) (g : U.toScheme ⟶ A),
          g ≫ (A ↘ S) = U.ι ≫ f ∧
            LocallyOfFiniteType g ∧ LocallyQuasiFinite g ∧
              AlgebraicGeometry.Gorenstein g,
        ∀ (U : X.Opens) (hxU : x ∈ U) (g : U.toScheme ⟶ A),
          g ≫ (A ↘ S) = U.ι ≫ f →
            AlgebraicGeometry.Scheme.Hom.FiniteType.QuasiFiniteAt g ⟨x, hxU⟩ →
              g.gorensteinAt ⟨x, hxU⟩
      ])

/- Lemma 48.25.11 (2): the Gorenstein locus of a flat, locally finitely
presented morphism is open. -/
@[stacks 0C09] #check
  (AlgebraicGeometry.Scheme.Hom.isOpen_gorensteinLocus_of_locallyOfFinitePresentation :
    ∀ {X S : Scheme} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f],
      IsOpen (AlgebraicGeometry.Scheme.Hom.gorensteinLocus f))
