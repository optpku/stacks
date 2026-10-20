module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage.Valuation
import StacksCheckRecall

/-!
# Lemma 29.6.5

Valuative realization of points of a quasi-compact scheme-theoretic image.

@stack 02JQ
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 29.6.5: a point of the scheme-theoretic image of a quasi-compact morphism
admits a valuative realization whose generic point lifts to the source. -/
@[stacks 02JQ] #check
  (AlgebraicGeometry.exists_valuationRing_diagram_of_mem_schemeTheoreticImage :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
      (z : Scheme.Hom.image f),
      ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : ValuationRing A)
        (K : Type u) (_ : Field K) (_ : Algebra A K) (_ : IsFractionRing A K)
        (genericToX : Spec (CommRingCat.of K) ⟶ X)
        (valuationToImage : Spec (CommRingCat.of A) ⟶ Scheme.Hom.image f),
          CommSq genericToX
            (Spec.map (CommRingCat.ofHom (algebraMap A K)))
            (Scheme.Hom.toImage f) valuationToImage ∧
          valuationToImage (IsLocalRing.closedPoint A) = z)

/- Consequently, every point of the scheme-theoretic image is a specialization of an
actual image point. -/
#check
  (AlgebraicGeometry.exists_specialization_from_image_of_mem_schemeTheoreticImage :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
      (z : Scheme.Hom.image f),
      ∃ x : X, Scheme.Hom.toImage f x ⤳ z)
