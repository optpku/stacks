module

public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import ReasLib.AlgebraicGeometry.GroupoidScheme.AffineNorm
public import ReasLib.AlgebraicGeometry.GroupoidScheme.FiniteLocallyFree

/-!
# Integrality for affine groupoid schemes

This module records integrality of an affine groupoid scheme's object ring over its invariant
equalizer subring when the source and target are finite locally free.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- For an affine presentation of a groupoid scheme whose source and target are finite locally
free, the object ring is integral over the equalizer subring of invariant elements. -/
theorem isIntegral_over_invariantRing {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (tSharp : A →+* B)
    (eU : Spec (CommRingCat.of A) ≅ G.U.left) (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom tSharp) ≫ eU.hom)
    [IsFiniteLocallyFree G.s.left] [IsFiniteLocallyFree G.t.left] :
    (algebraMap (tSharp.eqLocus (algebraMap A B)) A).IsIntegral := sorry

end AlgebraicGeometry.GroupoidScheme
