module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.Defs

/-!
# Monomorphisms into zero-dimensional local spectra

Monomorphisms of algebraic spaces into small disjoint unions of spectra of
zero-dimensional local rings are representable by schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- A monomorphism of algebraic spaces into the algebraic space associated to
the spectrum of a zero-dimensional local ring over `S` is representable. -/
theorem relativelyRepresentable_of_mono_to_zeroDimensionalLocalSpec
    {S : Scheme.{u}} {A : Type u}
    [CommRing A] [IsLocalRing A] [Ring.KrullDimLE 0 A] (σ : Spec (.of A) ⟶ S)
    {X : AlgebraicSpace S} (f : X ⟶ ofOver (Over.mk σ)) [Mono f] :
    yoneda.relativelyRepresentable f :=
  sorry

/-- A monomorphism of algebraic spaces into a small disjoint union of spectra
of zero-dimensional local rings over `S` is representable by schemes. -/
theorem relativelyRepresentable_of_mono_to_zeroDimensionalLocalCoproduct
    {S : Scheme.{u}} {ι : Type v} [Small.{u} ι]
    {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, IsLocalRing (A i)]
    [∀ i, Ring.KrullDimLE 0 (A i)] (σ : ∀ i, Spec (.of (A i)) ⟶ S)
    {X Y : AlgebraicSpace S} (e : Y ≅ ofOver (Over.mk (Sigma.desc σ)))
    (f : X ⟶ Y) [Mono f] : yoneda.relativelyRepresentable f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
