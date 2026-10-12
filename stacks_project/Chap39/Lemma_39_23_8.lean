/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.AffineInvariantBasis
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.GroupoidScheme

/- Lemma 39.23.8 (1): the target-basis family is linearly independent over the
invariant equalizer ring. -/
@[stacks 03C8] #check
  (AlgebraicGeometry.GroupoidScheme.linearIndependent_over_invariantRing :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S)
      {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
      (tSharp : A →+* B)
      (eU : Spec (CommRingCat.of A) ≅ G.U.left)
      (eR : Spec (CommRingCat.of B) ≅ G.R.left)
      (h_source : eR.hom ≫ G.s.left =
        Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
      (h_target : eR.hom ≫ G.t.left =
        Spec.map (CommRingCat.ofHom tSharp) ≫ eU.hom)
      {I : Type v} (x : I → A) (b : Module.Basis I A B)
      (h_basis : ∀ i, b i = tSharp (x i)),
      LinearIndependent (tSharp.eqLocus (algebraMap A B)) x)

/- Lemma 39.23.8 (2): the target-basis family spans the object ring over the
invariant equalizer ring. -/
@[stacks 03C8] #check
  (AlgebraicGeometry.GroupoidScheme.span_over_invariantRing_eq_top :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S)
      {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
      (tSharp : A →+* B)
      (eU : Spec (CommRingCat.of A) ≅ G.U.left)
      (eR : Spec (CommRingCat.of B) ≅ G.R.left)
      (h_source : eR.hom ≫ G.s.left =
        Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
      (h_target : eR.hom ≫ G.t.left =
        Spec.map (CommRingCat.ofHom tSharp) ≫ eU.hom)
      {I : Type v} (x : I → A) (b : Module.Basis I A B)
      (h_basis : ∀ i, b i = tSharp (x i)),
      Submodule.span (tSharp.eqLocus (algebraMap A B)) (Set.range x) = ⊤)

/- Lemma 39.23.8 (3): the canonical tensor-square comparison over the invariant
equalizer ring is bijective. -/
@[stacks 03C8] #check
  (AlgebraicGeometry.GroupoidScheme.invariantTensorSquare_bijective :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S)
      {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
      (tSharp : A →+* B)
      (eU : Spec (CommRingCat.of A) ≅ G.U.left)
      (eR : Spec (CommRingCat.of B) ≅ G.R.left)
      (h_source : eR.hom ≫ G.s.left =
        Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
      (h_target : eR.hom ≫ G.t.left =
        Spec.map (CommRingCat.ofHom tSharp) ≫ eU.hom)
      {I : Type v} (x : I → A) (b : Module.Basis I A B)
      (h_basis : ∀ i, b i = tSharp (x i)),
      Function.Bijective
        (Algebra.TensorProduct.RingHom.eqLocusSquare tSharp
          (algebraMap A B)).map)

end AlgebraicGeometry.GroupoidScheme
