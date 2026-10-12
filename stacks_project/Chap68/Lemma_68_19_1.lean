/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver

/-!
# Monomorphisms into disjoint unions of zero-dimensional local spectra

A monomorphism of algebraic spaces into a disjoint union of spectra of
zero-dimensional local rings over a scheme is representable by a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.19.1: Let `S` be a scheme. Let `Y` be a disjoint union of spectra of
zero-dimensional local rings over `S`. Let `f : X ⟶ Y` be a monomorphism of
algebraic spaces over `S`. Then `f` is representable, i.e., `X` is a scheme. -/
@[stacks 06RZ]
theorem relativelyRepresentable_of_mono {S : Scheme.{u}} {ι : Type v} [Small.{u} ι]
    {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, IsLocalRing (A i)]
    [∀ i, Ring.KrullDimLE 0 (A i)] (σ : ∀ i, Spec (.of (A i)) ⟶ S)
    {X Y : AlgebraicSpace S} (e : Y ≅ ofOver (Over.mk (Sigma.desc σ)))
    (f : X ⟶ Y) [Mono f] : yoneda.relativelyRepresentable f :=
  sorry

/-- A monomorphism of algebraic spaces into the algebraic space associated to
the spectrum of a zero-dimensional local ring over `S` is representable. -/
theorem relativelyRepresentable_of_mono_of_spec {S : Scheme.{u}} {A : Type u}
    [CommRing A] [IsLocalRing A] [Ring.KrullDimLE 0 A] (σ : Spec (.of A) ⟶ S)
    {X : AlgebraicSpace S} (f : X ⟶ ofOver (Over.mk σ)) [Mono f] :
    yoneda.relativelyRepresentable f :=
  sorry

/-- If `Y` is a disjoint union of spectra of zero-dimensional local rings over `S`
and `f : X ⟶ Y` is a monomorphism of algebraic spaces over `S`, then the functor
of points of `X` is representable. -/
theorem functorOfPoints_isRepresentable_of_mono {S : Scheme.{u}} {ι : Type v}
    [Small.{u} ι] {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, IsLocalRing (A i)]
    [∀ i, Ring.KrullDimLE 0 (A i)] (σ : ∀ i, Spec (.of (A i)) ⟶ S)
    {X Y : AlgebraicSpace S} (e : Y ≅ ofOver (Over.mk (Sigma.desc σ)))
    (f : X ⟶ Y) [Mono f] : X.functorOfPoints.IsRepresentable :=
  sorry

/-- If `Y` is a disjoint union of spectra of zero-dimensional local rings over `S`
and `f : X ⟶ Y` is a monomorphism of algebraic spaces over `S`, then `X` is
isomorphic to the algebraic space associated to a scheme over `S`. -/
theorem exists_iso_ofOver_of_mono {S : Scheme.{u}} {ι : Type v} [Small.{u} ι]
    {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, IsLocalRing (A i)]
    [∀ i, Ring.KrullDimLE 0 (A i)] (σ : ∀ i, Spec (.of (A i)) ⟶ S)
    {X Y : AlgebraicSpace S} (e : Y ≅ ofOver (Over.mk (Sigma.desc σ)))
    (f : X ⟶ Y) [Mono f] : ∃ T : Over S, Nonempty (X ≅ ofOver T) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
