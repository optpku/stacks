module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticImage.Valuation
import StacksCheckRecall

/-!
# Valuative realization of points of scheme-theoretic images

A point of the scheme-theoretic image of a quasi-compact morphism of algebraic
spaces is realized by a valuation ring whose generic point lifts to the source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

open AlgebraicSpace

/- Lemma 67.16.5: Every point of the scheme-theoretic image of a quasi-compact
morphism of algebraic spaces admits a valuative realization whose generic point
lifts to the source. -/
@[stacks 089B] #check
  (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage.exists_valuationRing_diagram :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
      (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
      [QuasiCompact f] [IsSchemeTheoreticImage f toImage ι] (z : Points Z),
      ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : ValuationRing A)
        (K : Type u) (_ : Field K) (_ : Algebra A K) (_ : IsFractionRing A K)
        (σ : Spec (.of A) ⟶ S)
        (genericToX :
          ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ σ)) ⟶ X)
        (valuationToImage : ofOver (Over.mk σ) ⟶ Z),
        CommSq genericToX (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A K))) rfl)
            toImage valuationToImage ∧
          Points.mapOfOver valuationToImage (IsLocalRing.closedPoint A) = z)
