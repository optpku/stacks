module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ConstructibleTorFinite.FiniteRing
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Frobenius.Derived
public import Mathlib.RingTheory.Noetherian.Basic

/-! # Perfect geometric cohomology of constructible Tor-finite complexes -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

noncomputable section

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

section RingCoefficients

variable {Λ : Type u} [Ring Λ] [Finite Λ]
variable [∀ Y : Scheme.{u}, HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ (Y : Scheme.{u}) (U : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ Y : Scheme.{u},
    HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z) (P : Z.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
    (smallEtalePullback f).op.HasLeftKanExtension P]

/-- Every geometric cohomology module of a constructible Tor-finite complex on a
projective curve over a field is finitely generated over the finite coefficient ring. -/
theorem geometricRGamma_homology_finite_of_constructibleTorFinite
    (X : SchemeOverField k) [Curve X] [Projective X.hom]
    (K : Scheme.Etale.Derived.FiniteRing.ConstructibleTorFinite (X := X.left) (Λ := Λ)) :
    ∀ i : ℤ, Module.Finite Λ
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} Λ) i).obj
        (geometricRGamma X K.obj)) := sorry

/-- Geometric derived global sections of a constructible Tor-finite complex on a
projective curve over a field form a perfect complex over the finite coefficient ring. -/
theorem isPerfect_geometricRGamma_of_constructibleTorFinite
    (X : SchemeOverField k) [Curve X] [Projective X.hom]
    (K : Scheme.Etale.Derived.FiniteRing.ConstructibleTorFinite (X := X.left) (Λ := Λ)) :
    DerivedCategory.IsPerfect (geometricRGamma X K.obj) := sorry

end RingCoefficients

section CommutativeCoefficients

variable {Λ : Type u} [CommRing Λ] [Finite Λ]
variable [∀ Y : Scheme.{u}, HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ (Y : Scheme.{u}) (U : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ Y : Scheme.{u},
    HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z) (P : Z.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
    (smallEtalePullback f).op.HasLeftKanExtension P]

/-- Geometric derived global sections of a constructible Tor-finite complex on a
projective curve over a field have finite Tor dimension over the finite commutative
coefficient ring. -/
theorem geometricRGamma_hasFiniteTorDimension_of_constructibleTorFinite
    (X : SchemeOverField k) [Curve X] [Projective X.hom]
    (K : Scheme.Etale.Derived.FiniteRing.ConstructibleTorFinite (X := X.left) (Λ := Λ)) :
    CategoryTheory.DerivedCategory.HasFiniteTorDimension Λ (geometricRGamma X K.obj) := sorry

end CommutativeCoefficients

end AlgebraicGeometry.SchemeOverField
