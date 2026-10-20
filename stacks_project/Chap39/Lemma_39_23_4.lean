module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.AffineIntegral
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 39.23.4: for an affine groupoid scheme whose source and target are finite locally
free, the object ring is integral over the invariant equalizer subring. -/
@[stacks 03BJ] #check
  (AlgebraicGeometry.GroupoidScheme.isIntegral_over_invariantRing :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
      {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (tSharp : A →+* B)
      (eU : AlgebraicGeometry.Spec (CommRingCat.of A) ≅ G.U.left)
      (eR : AlgebraicGeometry.Spec (CommRingCat.of B) ≅ G.R.left)
      (h_source : eR.hom ≫ G.s.left =
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
      (h_target : eR.hom ≫ G.t.left =
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom tSharp) ≫ eU.hom)
      [AlgebraicGeometry.IsFiniteLocallyFree G.s.left]
      [AlgebraicGeometry.IsFiniteLocallyFree G.t.left],
      (algebraMap (tSharp.eqLocus (algebraMap A B)) A).IsIntegral)
