/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.InvariantSpectrum.Etale
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry.Scheme.PreRelation

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/- Lemma 39.23.7 (1): for an étale morphism of affine groupoid schemes whose source,
target, and stabilizer squares are cartesian and whose endpoint maps are finite locally
free, the induced homomorphism on rings of invariant functions is étale. -/
@[stacks 0DT9]
#check (AlgebraicGeometry.GroupoidScheme.Hom.invariantRingMap_etale :
  ∀ {S : Scheme.{u}} {G G' : GroupoidScheme S}
    (F : Hom G' G) {A B A' B' : Type u}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] [Algebra A' B'] (target : A →+* B) (target' : A' →+* B')
    (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (eU' : Spec (CommRingCat.of A') ≅ G'.U.left)
    (eR' : Spec (CommRingCat.of B') ≅ G'.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom target) ≫ eU.hom)
    (h_source' : eR'.hom ≫ G'.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A' B')) ≫ eU'.hom)
    (h_target' : eR'.hom ≫ G'.t.left =
      Spec.map (CommRingCat.ofHom target') ≫ eU'.hom)
    [IsFiniteLocallyFree G.s.left] [IsFiniteLocallyFree G.t.left]
    [IsFiniteLocallyFree G'.s.left] [IsFiniteLocallyFree G'.t.left]
    (h_source_cartesian : IsPullback F.arrow.left G'.s.left G.s.left F.obj.left)
    (h_target_cartesian : IsPullback F.arrow.left G'.t.left G.t.left F.obj.left)
    (h_stabilizer_cartesian : IsPullback F.stabilizerMap.left
      G'.toPreRelation.stabilizer.hom.left G.toPreRelation.stabilizer.hom.left F.obj.left)
    [Etale F.obj.left],
    (F.invariantRingMap target target' eU eR eU' eR' h_source h_target h_source'
      h_target').Etale)

/- Lemma 39.23.7 (2): under the same affine, finite-locally-free, cartesian, and étale
hypotheses, the object scheme of the source groupoid is the pullback of the target object
scheme along the induced morphism of invariant spectra. -/
@[stacks 0DT9]
#check (AlgebraicGeometry.GroupoidScheme.Hom.invariantSpectrumSquare_isPullback :
  ∀ {S : Scheme.{u}} {G G' : GroupoidScheme S}
    (F : Hom G' G) {A B A' B' : Type u}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] [Algebra A' B'] (target : A →+* B) (target' : A' →+* B')
    (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (eU' : Spec (CommRingCat.of A') ≅ G'.U.left)
    (eR' : Spec (CommRingCat.of B') ≅ G'.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom target) ≫ eU.hom)
    (h_source' : eR'.hom ≫ G'.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A' B')) ≫ eU'.hom)
    (h_target' : eR'.hom ≫ G'.t.left =
      Spec.map (CommRingCat.ofHom target') ≫ eU'.hom)
    [IsFiniteLocallyFree G.s.left] [IsFiniteLocallyFree G.t.left]
    [IsFiniteLocallyFree G'.s.left] [IsFiniteLocallyFree G'.t.left]
    (h_source_cartesian : IsPullback F.arrow.left G'.s.left G.s.left F.obj.left)
    (h_target_cartesian : IsPullback F.arrow.left G'.t.left G.t.left F.obj.left)
    (h_stabilizer_cartesian : IsPullback F.stabilizerMap.left
      G'.toPreRelation.stabilizer.hom.left G.toPreRelation.stabilizer.hom.left F.obj.left)
    [Etale F.obj.left],
    IsPullback F.obj.left (invariantSpectrumMap G' target' eU')
      (invariantSpectrumMap G target eU)
      (Spec.map (CommRingCat.ofHom (F.invariantRingMap target target' eU eR eU' eR'
        h_source h_target h_source' h_target'))))

end AlgebraicGeometry.GroupoidScheme
