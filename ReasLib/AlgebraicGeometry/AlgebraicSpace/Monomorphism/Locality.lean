/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Monomorphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiCover.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Locality of monomorphisms of algebraic spaces

Monomorphisms of algebraic spaces are tested on scheme-valued base changes,
surjective étale scheme atlases, and Zariski coverings of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Monomorphisms

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- The base change of `f` along every morphism from a scheme over `S` is a
monomorphism. -/
def forallScheme : Prop :=
  ∀ {Z : Over S} {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Mono pZ

/-- `forallScheme f` means every scheme-valued pullback projection of `f` is a
monomorphism. -/
theorem forallScheme_iff : forallScheme f ↔
    ∀ (Z : Over S) (P : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : P ⟶ ofOver Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → Mono pZ := Iff.rfl

/-- The base change of `f` along every morphism from an affine scheme over `S`
is a monomorphism. -/
def forallAffine : Prop :=
  ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Mono pZ

/-- `forallAffine f` means every affine-scheme-valued pullback projection of `f`
is a monomorphism. -/
theorem forallAffine_iff : forallAffine f ↔
    ∀ (Z : Over S) [IsAffine Z.left] (P : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : P ⟶ ofOver Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → Mono pZ := Iff.rfl

/-- There is a surjective étale morphism from a scheme to `Y` along which every
pullback of `f` is a monomorphism. -/
def existsEtaleOnTarget : Prop :=
  ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
    Etale ψ ∧ Surjective ψ ∧
      ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
        IsPullback pV pX ψ f → Mono pV

/-- `existsEtaleOnTarget f` is the existence of a surjective étale scheme atlas
of `Y` along which pullbacks of `f` are monomorphisms. -/
theorem existsEtaleOnTarget_iff : existsEtaleOnTarget f ↔
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ (P : AlgebraicSpace S) (pV : P ⟶ ofOver V) (pX : P ⟶ X),
          IsPullback pV pX ψ f → Mono pV := Iff.rfl

/-- There is a Zariski covering of `Y` along which every inverse-image
projection of `f` is a monomorphism. -/
def existsZariskiCover : Prop :=
  ∃ (𝒰 : ZariskiCover.{u, u} Y),
    ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → Mono pYi

/-- `existsZariskiCover f` is the existence of a Zariski covering of `Y` whose
inverse images under `f` map monomorphically to the covering opens. -/
theorem existsZariskiCover_iff : existsZariskiCover f ↔
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i (P : AlgebraicSpace S) (pYi : P ⟶ 𝒰.X i) (pX : P ⟶ X),
        IsPullback pYi pX (𝒰.f i) f → Mono pYi := Iff.rfl

/-- For a morphism of algebraic spaces over a scheme, monicity is equivalent
to monicity after every scheme-valued base change, every affine-scheme-valued
base change, base change along some surjective étale scheme atlas of the target,
and restriction over some Zariski covering of the target. -/
theorem tfae :
    List.TFAE [Mono f, forallScheme f, forallAffine f, existsEtaleOnTarget f,
      existsZariskiCover f] := sorry

/-- A morphism of algebraic spaces is a monomorphism iff every scheme-valued
base change is a monomorphism. -/
theorem iff_forallScheme : Mono f ↔ forallScheme f := (tfae f).out 0 1

/-- A morphism of algebraic spaces is a monomorphism iff every
affine-scheme-valued base change is a monomorphism. -/
theorem iff_forallAffine : Mono f ↔ forallAffine f := (tfae f).out 0 2

/-- A morphism of algebraic spaces is a monomorphism iff some surjective étale
scheme atlas of the target has monomorphic pullback. -/
theorem iff_existsEtaleOnTarget : Mono f ↔ existsEtaleOnTarget f := (tfae f).out 0 3

/-- A morphism of algebraic spaces is a monomorphism iff some Zariski covering
of the target has monomorphic inverse images under `f`. -/
theorem iff_existsZariskiCover : Mono f ↔ existsZariskiCover f := (tfae f).out 0 4

end Monomorphisms

end AlgebraicGeometry.AlgebraicSpace
