module

public import ReasLib.AlgebraicGeometry.RingedSite.PolynomialAugmentation

/-!
# The polynomial site and its ringed-topos morphisms

The polynomial-site constructions are supplied by their shared mathematical owners.
The site and universe-lift abbreviations retain the presentation used by downstream files.
-/

@[expose] public section

open CategoryTheory

universe u

namespace CommAlgCat.Over.Polynomial

/-- The opposite category of polynomial algebra augmentations to a fixed target algebra. -/
abbrev site (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :=
  Algebra.PolynomialSite A B

namespace Site

/-- The commutative-ring functor that lifts coefficients to the next universe. -/
abbrev uliftCommRing : CommRingCat.{u} ⥤ CommRingCat.{u + 1} :=
  RingedSite.Cotangent.uliftCommRing

end Site

end CommAlgCat.Over.Polynomial

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

#check (Algebra.PolynomialSite.unop_isPolynomial :
  ∀ (X : Algebra.PolynomialSite A B), Algebra.IsPolynomial A X.unop.obj.left)
#check (CommAlgCat.Over.Polynomial.Site.i A B :
  RingedSite.ToposHom (CommAlgCat.Over.Polynomial.Site.constantRingedSite A B)
    (CommAlgCat.Over.Polynomial.Site.ringedSite A B))
#check (CommAlgCat.Over.Polynomial.Site.toPoint A B :
  RingedSite.ToposHom (CommAlgCat.Over.Polynomial.Site.constantRingedSite A B)
    (CommAlgCat.Over.Polynomial.Site.pointRingedSite B))
