/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.Basis.Basic
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Pullback
public import ReasLib.RingTheory.Algebra.TensorProduct.EqLocus
import ReasLib.Algebra.Amitsur.Acyclic

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.GroupoidScheme

/-- If the target images of a family form a basis of the arrow ring over the
object ring, then the family is linearly independent over the invariant
equalizer subring. -/
theorem linearIndependent_over_invariantRing {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (tSharp : A →+* B)
    (eU : Spec (CommRingCat.of A) ≅ G.U.left) (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom tSharp) ≫ eU.hom)
    {I : Type v} (x : I → A) (b : Module.Basis I A B) (h_basis : ∀ i, b i = tSharp (x i)) :
    LinearIndependent (tSharp.eqLocus (algebraMap A B)) x := sorry

/-- If the target images of a family form a basis of the arrow ring over the
object ring, then the family spans the object ring over the invariant
equalizer subring. -/
theorem span_over_invariantRing_eq_top {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (tSharp : A →+* B)
    (eU : Spec (CommRingCat.of A) ≅ G.U.left) (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom tSharp) ≫ eU.hom)
    {I : Type v} (x : I → A) (b : Module.Basis I A B) (h_basis : ∀ i, b i = tSharp (x i)) :
    Submodule.span (tSharp.eqLocus (algebraMap A B)) (Set.range x) = ⊤ := sorry

/-- If the target images of a family form a basis of the arrow ring over the
object ring, then the canonical tensor-square comparison over the invariant
equalizer subring is bijective. -/
theorem invariantTensorSquare_bijective {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (tSharp : A →+* B)
    (eU : Spec (CommRingCat.of A) ≅ G.U.left) (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom tSharp) ≫ eU.hom)
    {I : Type v} (x : I → A) (b : Module.Basis I A B) (h_basis : ∀ i, b i = tSharp (x i)) :
    Function.Bijective
      (Algebra.TensorProduct.RingHom.eqLocusSquare tSharp (algebraMap A B)).map := sorry

end AlgebraicGeometry.GroupoidScheme
