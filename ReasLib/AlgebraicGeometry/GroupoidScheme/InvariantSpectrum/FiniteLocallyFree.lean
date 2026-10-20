module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.EffectiveEpi
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import ReasLib.AlgebraicGeometry.GroupoidScheme.AffineInvariantBasis
public import ReasLib.AlgebraicGeometry.GroupoidScheme.InvariantBaseChange.FiniteLocallyFree

/-!
# Invariant spectra of finite locally free affine groupoid schemes

This module records the quotient properties of the invariant spectrum on underlying points
and on points valued in an algebraically closed field.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The canonical map from the object scheme of an affine groupoid scheme to its invariant
spectrum is surjective on underlying points when both endpoint maps are finite locally free. -/
theorem invariantSpectrumMap_surjective {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (tSharp : A →+* B)
    (eU : Spec (CommRingCat.of A) ≅ G.U.left) (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom tSharp) ≫ eU.hom)
    [IsFiniteLocallyFree G.s.left] [IsFiniteLocallyFree G.t.left] :
    Function.Surjective (invariantSpectrumMap G tSharp eU).base := sorry

/-- Over an algebraically closed field, every point of the invariant equalizer ring lifts to
a point of the affine object ring when both endpoint maps are finite locally free. -/
theorem invariantRingPoints_surjective {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (tSharp : A →+* B)
    (eU : Spec (CommRingCat.of A) ≅ G.U.left) (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom tSharp) ≫ eU.hom)
    [IsFiniteLocallyFree G.s.left] [IsFiniteLocallyFree G.t.left]
    {k : Type u} [Field k] [IsAlgClosed k] :
    Function.Surjective
      (fun a : A →+* k ↦ a.comp (tSharp.eqLocus (algebraMap A B)).subtype) := sorry

/-- Over an algebraically closed field, two points of the affine object ring restrict equally
to the invariant ring exactly when they are the target and source restrictions of a point of
the arrow ring. -/
theorem invariantRingPoints_eq_iff {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (tSharp : A →+* B)
    (eU : Spec (CommRingCat.of A) ≅ G.U.left) (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom tSharp) ≫ eU.hom)
    [IsFiniteLocallyFree G.s.left] [IsFiniteLocallyFree G.t.left]
    {k : Type u} [Field k] [IsAlgClosed k] (a₀ a₁ : A →+* k) :
    a₀.comp (tSharp.eqLocus (algebraMap A B)).subtype =
        a₁.comp (tSharp.eqLocus (algebraMap A B)).subtype ↔
      ∃ b : B →+* k, b.comp tSharp = a₀ ∧ b.comp (algebraMap A B) = a₁ := sorry

/-- Two underlying points of the object scheme have the same image in the invariant spectrum
exactly when they are the target and source of an underlying point of the arrow scheme. -/
theorem invariantSpectrumMap_apply_eq_iff {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (tSharp : A →+* B)
    (eU : Spec (CommRingCat.of A) ≅ G.U.left) (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom tSharp) ≫ eU.hom)
    [IsFiniteLocallyFree G.s.left] [IsFiniteLocallyFree G.t.left] (u₀ u₁ : G.U.left) :
    (invariantSpectrumMap G tSharp eU).base u₀ =
        (invariantSpectrumMap G tSharp eU).base u₁ ↔
      ∃ r : G.R.left, G.t.left r = u₀ ∧ G.s.left r = u₁ := sorry

/-- The canonical map from an affine finite locally free equivalence-relation groupoid to
the spectrum of its invariant equalizer ring is finite locally free. -/
theorem invariantSpectrumMap_isFiniteLocallyFree {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (tSharp : A →+* B)
    (eU : Spec (CommRingCat.of A) ≅ G.U.left) (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom tSharp) ≫ eU.hom)
    [IsFiniteLocallyFree G.s.left] [IsFiniteLocallyFree G.t.left]
    [IsEquivalenceRelation G.t G.s] :
    IsFiniteLocallyFree (invariantSpectrumMap G tSharp eU) := sorry

/-- The canonical map from an affine finite locally free equivalence-relation groupoid to
the spectrum of its invariant equalizer ring is an effective epimorphism. The descent
structure comes from the native construction for flat surjections between affine schemes. -/
theorem invariantSpectrumMap_effectiveEpi {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (tSharp : A →+* B)
    (eU : Spec (CommRingCat.of A) ≅ G.U.left) (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom tSharp) ≫ eU.hom)
    [IsFiniteLocallyFree G.s.left] [IsFiniteLocallyFree G.t.left]
    [IsEquivalenceRelation G.t G.s] :
    EffectiveEpi (invariantSpectrumMap G tSharp eU) :=
  let objectAffine := IsAffine.of_isIso eU.inv
  let finiteLocallyFree :=
    invariantSpectrumMap_isFiniteLocallyFree G tSharp eU eR h_source h_target
  let surjective := invariantSpectrumMap_surjective G tSharp eU eR h_source h_target
  (isRegularEpi_iff_effectiveEpi (invariantSpectrumMap G tSharp eU)).mp
    (@isRegularEpi_of_flat_of_surjective_of_isAffine _ _ objectAffine (isAffine_Spec _)
      (invariantSpectrumMap G tSharp eU) ⟨surjective⟩ finiteLocallyFree.flat)

end AlgebraicGeometry.GroupoidScheme
