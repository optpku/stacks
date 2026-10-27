/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.RingTheory.RingHom.SmallExtension

/-!
# Infinitesimal lifting criteria for smoothness of algebraic spaces

For a locally finite-type morphism of algebraic spaces with locally Noetherian
target, smoothness at a point is equivalent to the infinitesimal lifting
property at that point against square-zero surjections of local rings, and
equivalently against small extensions. Global smoothness is equivalent to the
lifting property against small extensions of Artinian local rings whose bottom
arrow is of finite type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The morphism of algebraic spaces over `S` induced by `Spec.map` of a ring
homomorphism `π : B' →+* B`, relative to a structure morphism
`σ : Spec (CommRingCat.of B') ⟶ S`. -/
def ofOverSpecMap {S : Scheme.{u}} {B' B : Type u} [CommRing B'] [CommRing B]
    (π : B' →+* B) (σ : Spec (CommRingCat.of B') ⟶ S) :
    ofOver (Over.mk (Spec.map (CommRingCat.ofHom π) ≫ σ)) ⟶ ofOver (Over.mk σ) :=
  ofOverHomMk (Spec.map (CommRingCat.ofHom π)) rfl

/-- `ofOverSpecMap π σ` is `ofOverHomMk` of `Spec.map` of `π`. -/
theorem ofOverSpecMap_eq {S : Scheme.{u}} {B' B : Type u} [CommRing B'] [CommRing B]
    (π : B' →+* B) (σ : Spec (CommRingCat.of B') ⟶ S) :
    ofOverSpecMap π σ = ofOverHomMk (Spec.map (CommRingCat.ofHom π)) rfl :=
  rfl

/-- The infinitesimal lifting property of `f` at `x` against surjections of
local rings with square-zero kernel. -/
def HasSquareZeroLiftingAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X) : Prop :=
  ∀ (B' B : Type u) [CommRing B'] [CommRing B] [IsLocalRing B'] [IsLocalRing B]
    (π : B' →+* B) [π.IsSquareZeroExtension]
    (σ : Spec (CommRingCat.of B') ⟶ S)
    (α : ofOver (Over.mk (Spec.map (CommRingCat.ofHom π) ≫ σ)) ⟶ X)
    (β : ofOver (Over.mk σ) ⟶ Y),
    α ≫ f = ofOverSpecMap π σ ≫ β →
      Points.mapOfOver α (IsLocalRing.closedPoint B) = x →
        ∃ γ : ofOver (Over.mk σ) ⟶ X,
          ofOverSpecMap π σ ≫ γ = α ∧ γ ≫ f = β

/-- Unfolding of `HasSquareZeroLiftingAt`: every solid square against a
square-zero surjection of local rings whose top arrow sends the closed point of
`Spec (CommRingCat.of B)` to `x` admits a lift. -/
theorem hasSquareZeroLiftingAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X) :
    HasSquareZeroLiftingAt f x ↔
      ∀ (B' B : Type u) [CommRing B'] [CommRing B] [IsLocalRing B'] [IsLocalRing B]
        (π : B' →+* B) [π.IsSquareZeroExtension]
        (σ : Spec (CommRingCat.of B') ⟶ S)
        (α : ofOver (Over.mk (Spec.map (CommRingCat.ofHom π) ≫ σ)) ⟶ X)
        (β : ofOver (Over.mk σ) ⟶ Y),
        α ≫ f = ofOverSpecMap π σ ≫ β →
          Points.mapOfOver α (IsLocalRing.closedPoint B) = x →
            ∃ γ : ofOver (Over.mk σ) ⟶ X,
              ofOverSpecMap π σ ≫ γ = α ∧ γ ≫ f = β :=
  Iff.rfl

/-- The infinitesimal lifting property of `f` at `x` against small extensions. -/
def HasSmallExtensionLiftingAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X) : Prop :=
  ∀ (B' B : Type u) [CommRing B'] [CommRing B] [IsLocalRing B'] [IsLocalRing B]
    (π : B' →+* B) [π.IsSmallExtension]
    (σ : Spec (CommRingCat.of B') ⟶ S)
    (α : ofOver (Over.mk (Spec.map (CommRingCat.ofHom π) ≫ σ)) ⟶ X)
    (β : ofOver (Over.mk σ) ⟶ Y),
    α ≫ f = ofOverSpecMap π σ ≫ β →
      Points.mapOfOver α (IsLocalRing.closedPoint B) = x →
        ∃ γ : ofOver (Over.mk σ) ⟶ X,
          ofOverSpecMap π σ ≫ γ = α ∧ γ ≫ f = β

/-- Unfolding of `HasSmallExtensionLiftingAt`: every solid square against a
small extension whose top arrow sends the closed point of
`Spec (CommRingCat.of B)` to `x` admits a lift. -/
theorem hasSmallExtensionLiftingAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X) :
    HasSmallExtensionLiftingAt f x ↔
      ∀ (B' B : Type u) [CommRing B'] [CommRing B] [IsLocalRing B'] [IsLocalRing B]
        (π : B' →+* B) [π.IsSmallExtension]
        (σ : Spec (CommRingCat.of B') ⟶ S)
        (α : ofOver (Over.mk (Spec.map (CommRingCat.ofHom π) ≫ σ)) ⟶ X)
        (β : ofOver (Over.mk σ) ⟶ Y),
        α ≫ f = ofOverSpecMap π σ ≫ β →
          Points.mapOfOver α (IsLocalRing.closedPoint B) = x →
            ∃ γ : ofOver (Over.mk σ) ⟶ X,
              ofOverSpecMap π σ ≫ γ = α ∧ γ ≫ f = β :=
  Iff.rfl

/-- For a locally finite-type morphism of algebraic spaces to a locally
Noetherian target, smoothness at a point is equivalent to the infinitesimal
lifting property at that point against square-zero local surjections and
against small extensions. -/
theorem smoothAt_tfae_infinitesimalLifting {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] :
    List.TFAE
      [ SmoothAt f x
      , HasSquareZeroLiftingAt f x
      , HasSmallExtensionLiftingAt f x ] :=
  sorry

/-- Smoothness at a point is equivalent to lifting against square-zero
surjections of local rings. -/
theorem smoothAt_iff_hasSquareZeroLiftingAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] :
    SmoothAt f x ↔ HasSquareZeroLiftingAt f x :=
  (smoothAt_tfae_infinitesimalLifting f x).out 0 1

/-- Smoothness at a point is equivalent to lifting against small extensions. -/
theorem smoothAt_iff_hasSmallExtensionLiftingAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] :
    SmoothAt f x ↔ HasSmallExtensionLiftingAt f x :=
  (smoothAt_tfae_infinitesimalLifting f x).out 0 2

/-- The infinitesimal lifting property of `f` against small extensions of
Artinian local rings whose bottom arrow is of finite type. -/
def HasFiniteTypeSmallExtensionLifting {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∀ (B' B : Type u) [CommRing B'] [CommRing B] (π : B' →+* B) [π.IsSmallExtension]
    (σ : Spec (CommRingCat.of B') ⟶ S)
    (α : ofOver (Over.mk (Spec.map (CommRingCat.ofHom π) ≫ σ)) ⟶ X)
    (β : ofOver (Over.mk σ) ⟶ Y) [FiniteType β],
    CommSq α (ofOverSpecMap π σ) f β →
      ∃ γ : ofOver (Over.mk σ) ⟶ X, ofOverSpecMap π σ ≫ γ = α ∧ γ ≫ f = β

/-- Unfolding of `HasFiniteTypeSmallExtensionLifting`: every solid square
against a small extension whose bottom arrow is of finite type admits a lift. -/
theorem hasFiniteTypeSmallExtensionLifting_iff {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    HasFiniteTypeSmallExtensionLifting f ↔
      ∀ (B' B : Type u) [CommRing B'] [CommRing B] (π : B' →+* B) [π.IsSmallExtension]
        (σ : Spec (CommRingCat.of B') ⟶ S)
        (α : ofOver (Over.mk (Spec.map (CommRingCat.ofHom π) ≫ σ)) ⟶ X)
        (β : ofOver (Over.mk σ) ⟶ Y) [FiniteType β],
        CommSq α (ofOverSpecMap π σ) f β →
          ∃ γ : ofOver (Over.mk σ) ⟶ X, ofOverSpecMap π σ ≫ γ = α ∧ γ ≫ f = β :=
  Iff.rfl

/-- A locally finite-type morphism of algebraic spaces to a locally Noetherian
target is smooth if and only if every solid square against a small extension
whose bottom arrow is of finite type admits a lift. -/
theorem smooth_iff_smallExtensionLifting {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsLocallyNoetherian Y] [LocallyOfFiniteType f] :
    Smooth f ↔ HasFiniteTypeSmallExtensionLifting f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
