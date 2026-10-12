/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import ReasLib.RingTheory.RingHom.SmallExtension

/-!
# Infinitesimal lifting criterion for smoothness at a point of an algebraic space

For a locally finite-type morphism of algebraic spaces with locally Noetherian
target, smoothness at a point is equivalent to the infinitesimal lifting
property at that point against square-zero surjections of local rings, and
equivalently against small extensions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The morphism of algebraic spaces over `S` induced by `Spec.map` of a ring
homomorphism `π : B' →+* B`, relative to a structure morphism
`σ : Spec (CommRingCat.of B') ⟶ S`. -/
def specMapOver {S : Scheme.{u}} {B' B : Type u} [CommRing B'] [CommRing B]
    (π : B' →+* B) (σ : Spec (CommRingCat.of B') ⟶ S) :
    ofOver (Over.mk (Spec.map (CommRingCat.ofHom π) ≫ σ)) ⟶ ofOver (Over.mk σ) :=
  ofOverHomMk (Spec.map (CommRingCat.ofHom π)) rfl

/-- `specMapOver π σ` is `ofOverHomMk` of `Spec.map` of `π`. -/
theorem specMapOver_eq {S : Scheme.{u}} {B' B : Type u} [CommRing B'] [CommRing B]
    (π : B' →+* B) (σ : Spec (CommRingCat.of B') ⟶ S) :
    specMapOver π σ = ofOverHomMk (Spec.map (CommRingCat.ofHom π)) rfl :=
  sorry

/-- The infinitesimal lifting property of `f` at `x` against surjections of
local rings with square-zero kernel. -/
def HasSquareZeroLiftingAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X) : Prop :=
  ∀ (B' B : Type u) [CommRing B'] [CommRing B] [IsLocalRing B'] [IsLocalRing B]
    (π : B' →+* B) [π.IsSquareZeroExtension]
    (σ : Spec (CommRingCat.of B') ⟶ S)
    (α : ofOver (Over.mk (Spec.map (CommRingCat.ofHom π) ≫ σ)) ⟶ X)
    (β : ofOver (Over.mk σ) ⟶ Y),
    α ≫ f = specMapOver π σ ≫ β →
      Points.mapOfOver α (IsLocalRing.closedPoint B) = x →
        ∃ γ : ofOver (Over.mk σ) ⟶ X,
          specMapOver π σ ≫ γ = α ∧ γ ≫ f = β

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
        α ≫ f = specMapOver π σ ≫ β →
          Points.mapOfOver α (IsLocalRing.closedPoint B) = x →
            ∃ γ : ofOver (Over.mk σ) ⟶ X,
              specMapOver π σ ≫ γ = α ∧ γ ≫ f = β :=
  sorry

/-- The infinitesimal lifting property of `f` at `x` against small extensions. -/
def HasSmallExtensionLiftingAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X) : Prop :=
  ∀ (B' B : Type u) [CommRing B'] [CommRing B] [IsLocalRing B'] [IsLocalRing B]
    (π : B' →+* B) [π.IsSmallExtension]
    (σ : Spec (CommRingCat.of B') ⟶ S)
    (α : ofOver (Over.mk (Spec.map (CommRingCat.ofHom π) ≫ σ)) ⟶ X)
    (β : ofOver (Over.mk σ) ⟶ Y),
    α ≫ f = specMapOver π σ ≫ β →
      Points.mapOfOver α (IsLocalRing.closedPoint B) = x →
        ∃ γ : ofOver (Over.mk σ) ⟶ X,
          specMapOver π σ ≫ γ = α ∧ γ ≫ f = β

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
        α ≫ f = specMapOver π σ ≫ β →
          Points.mapOfOver α (IsLocalRing.closedPoint B) = x →
            ∃ γ : ofOver (Over.mk σ) ⟶ X,
              specMapOver π σ ≫ γ = α ∧ γ ≫ f = β :=
  sorry

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
  sorry

/-- Smoothness at a point is equivalent to lifting against small extensions. -/
theorem smoothAt_iff_hasSmallExtensionLiftingAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] :
    SmoothAt f x ↔ HasSmallExtensionLiftingAt f x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
