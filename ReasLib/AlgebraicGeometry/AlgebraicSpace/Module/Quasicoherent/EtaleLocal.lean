module

public import Mathlib.Data.List.TFAE
public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points

/-!
# Étale-local characterizations of quasi-coherence

Quasi-coherence of an `𝒪_X`-module on an algebraic space is tested after pullback
along étale morphisms from algebraic spaces, from schemes, and from affine schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

namespace IsQuasicoherent

/-- There exists an étale morphism of algebraic spaces over `S` whose induced map on
points is surjective, along which the pullback of `F` is quasi-coherent. -/
def existsEtale {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) : Prop :=
  ∃ (Y : AlgebraicSpace S) (f : Y ⟶ X) (hf : Etale f),
    Function.Surjective (Points.map f) ∧ ((pullback f).obj F).IsQuasicoherent

/-- `existsEtale F` is the existence of a surjective étale algebraic-space cover along
which the pullback of `F` is quasi-coherent. -/
theorem existsEtale_def {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) :
    existsEtale F ↔
      ∃ (Y : AlgebraicSpace S) (f : Y ⟶ X) (hf : Etale f),
        Function.Surjective (Points.map f) ∧ ((pullback f).obj F).IsQuasicoherent :=
  Iff.rfl

namespace existsEtale

/-- A surjective étale morphism of algebraic spaces along which the pullback of `F` is
quasi-coherent witnesses `existsEtale F`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {F : X.Modules} {Y : AlgebraicSpace S}
    (f : Y ⟶ X) [Etale f] (h_surj : Function.Surjective (Points.map f))
    (hF : ((pullback f).obj F).IsQuasicoherent) : existsEtale F :=
  ⟨Y, f, ‹Etale f›, h_surj, hF⟩

/-- An `𝒪_X`-module satisfying `existsEtale F` admits a surjective étale algebraic-space
cover along which its pullback is quasi-coherent. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} {F : X.Modules} (h : existsEtale F) :
    ∃ (Y : AlgebraicSpace S) (f : Y ⟶ X) (hf : Etale f),
      Function.Surjective (Points.map f) ∧ ((pullback f).obj F).IsQuasicoherent :=
  h

end existsEtale

/-- There exists a scheme `U` over `S` and a surjective étale morphism `φ : U ⟶ X` such
that the pullback of `F` is quasi-coherent on `U`. -/
def existsScheme {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) : Prop :=
  ∃ (U : Over S) (φ : ofOver U ⟶ X) (hφ : Etale φ),
    Function.Surjective (Points.map φ) ∧
      ((pullback φ).obj F).IsQuasicoherent

/-- `existsScheme F` is the existence of a surjective étale scheme atlas along which the
pullback of `F` is quasi-coherent. -/
theorem existsScheme_def {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) :
    existsScheme F ↔
      ∃ (U : Over S) (φ : ofOver U ⟶ X) (hφ : Etale φ),
        Function.Surjective (Points.map φ) ∧
          ((pullback φ).obj F).IsQuasicoherent :=
  Iff.rfl

namespace existsScheme

/-- A surjective étale scheme atlas along which the pullback of `F` is quasi-coherent
witnesses `existsScheme F`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {F : X.Modules} {U : Over S}
    (φ : ofOver U ⟶ X) [Etale φ]
    (h_surj : Function.Surjective (Points.map φ))
    (hF : ((pullback φ).obj F).IsQuasicoherent) : existsScheme F :=
  ⟨U, φ, ‹Etale φ›, h_surj, hF⟩

/-- An `𝒪_X`-module satisfying `existsScheme F` admits a surjective étale scheme atlas
along which its pullback is quasi-coherent. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} {F : X.Modules} (h : existsScheme F) :
    ∃ (U : Over S) (φ : ofOver U ⟶ X) (hφ : Etale φ),
      Function.Surjective (Points.map φ) ∧
        ((pullback φ).obj F).IsQuasicoherent :=
  h

end existsScheme

/-- For every affine scheme `U` over `S` and every étale morphism `φ : U ⟶ X`, the
pullback of `F` is quasi-coherent on `U`. -/
def forallAffine {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) : Prop :=
  ∀ (U : Over S) [IsAffine U.left] (φ : ofOver U ⟶ X) [Etale φ],
    ((pullback φ).obj F).IsQuasicoherent

/-- `forallAffine F` is the universal affine étale-scheme quasi-coherence condition. -/
theorem forallAffine_def {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) :
    forallAffine F ↔
      ∀ (U : Over S) [IsAffine U.left] (φ : ofOver U ⟶ X) [Etale φ],
        ((pullback φ).obj F).IsQuasicoherent :=
  Iff.rfl

namespace forallAffine

/-- The universal affine étale-scheme quasi-coherence condition witnesses `forallAffine F`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {F : X.Modules}
    (h : ∀ (U : Over S) [IsAffine U.left] (φ : ofOver U ⟶ X) [Etale φ],
      ((pullback φ).obj F).IsQuasicoherent) : forallAffine F :=
  h

/-- An `𝒪_X`-module satisfying `forallAffine F` has quasi-coherent pullback along every
étale morphism from an affine scheme. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} {F : X.Modules} (h : forallAffine F) :
    ∀ (U : Over S) [IsAffine U.left] (φ : ofOver U ⟶ X) [Etale φ],
      ((pullback φ).obj F).IsQuasicoherent :=
  h

/-- Pullback along a given étale morphism from an affine scheme is quasi-coherent. -/
theorem apply {S : Scheme.{u}} {X : AlgebraicSpace S} {F : X.Modules} (h : forallAffine F)
    {U : Over S} [IsAffine U.left] (φ : ofOver U ⟶ X) [Etale φ] :
    ((pullback φ).obj F).IsQuasicoherent :=
  h U φ

end forallAffine

end IsQuasicoherent

/-- Quasi-coherence of a module sheaf on an algebraic space is equivalent to
quasi-coherence after a surjective étale algebraic-space cover, after a surjective
étale scheme cover, and after every affine étale scheme morphism. -/
theorem isQuasicoherent_tfae {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) :
    List.TFAE [F.IsQuasicoherent, IsQuasicoherent.existsEtale F,
      IsQuasicoherent.existsScheme F, IsQuasicoherent.forallAffine F] :=
  sorry

namespace IsQuasicoherent

/-- Quasi-coherence of `F` is equivalent to the existence of a surjective étale
algebraic-space cover along which the pullback of `F` is quasi-coherent. -/
theorem iff_existsEtale {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) :
    F.IsQuasicoherent ↔ existsEtale F :=
  (isQuasicoherent_tfae F).out 0 1

/-- Quasi-coherence of `F` is equivalent to the existence of a surjective étale scheme
atlas along which the pullback of `F` is quasi-coherent. -/
theorem iff_existsScheme {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) :
    F.IsQuasicoherent ↔ existsScheme F :=
  (isQuasicoherent_tfae F).out 0 2

/-- Quasi-coherence of `F` is equivalent to quasi-coherence of its pullback along every
étale morphism from an affine scheme. -/
theorem iff_forallAffine {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) :
    F.IsQuasicoherent ↔ forallAffine F :=
  (isQuasicoherent_tfae F).out 0 3

end IsQuasicoherent

end AlgebraicGeometry.AlgebraicSpace.Modules
