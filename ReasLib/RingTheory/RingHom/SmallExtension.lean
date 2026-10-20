module

public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.RingHom.SquareZero

/-!
# Small Extensions of Local Artinian Rings

This leaf owns the deformation-theoretic notion of a small extension as a
property of a commutative ring homomorphism.  The source local-Artinian data,
surjectivity, and length-one kernel are primitive; locality, Artinianness, and
square-zero consequences are exposed separately for downstream lifting
arguments.

@stack 02HS
-/

@[expose] public section

universe u v

namespace RingHom

/-- A ring map `φ : B' →+* B` is a small extension when `B'` is a local
Artinian ring, `B` is nontrivial, `φ` is surjective, and `RingHom.ker φ` has length `1` as a
`B'`-module. -/
@[stacks 02HS]
class IsSmallExtension {B' : Type u} {B : Type v} [CommRing B'] [CommRing B]
    (φ : B' →+* B) : Prop where
  /-- The source of a small extension is local. -/
  [instIsLocalRingSource : IsLocalRing B']
  /-- The source of a small extension is Artinian. -/
  [instIsArtinianRingSource : IsArtinianRing B']
  /-- The target of a small extension is nontrivial. -/
  [instNontrivialTarget : Nontrivial B]
  /-- A small extension is surjective. -/
  surjective : Function.Surjective φ
  /-- The kernel of a small extension has module length one over its source. -/
  ker_length : Module.length B' (RingHom.ker φ) = 1

attribute [instance] IsSmallExtension.instIsLocalRingSource
attribute [instance] IsSmallExtension.instIsArtinianRingSource
attribute [instance] IsSmallExtension.instNontrivialTarget

namespace IsSmallExtension

/-- Every small extension is canonically a square-zero extension. -/
instance instIsSquareZeroExtension {B' : Type u} {B : Type v}
    [CommRing B'] [CommRing B] (phi : B' →+* B) [phi.IsSmallExtension] :
    phi.IsSquareZeroExtension := sorry

/-- The source of a small extension is a local ring. -/
theorem isLocalRingSource {B' : Type u} {B : Type v} [CommRing B'] [CommRing B]
    {φ : B' →+* B} [hφ : φ.IsSmallExtension] : IsLocalRing B' := sorry

/-- The source of a small extension is an Artinian ring. -/
theorem isArtinianRingSource {B' : Type u} {B : Type v} [CommRing B'] [CommRing B]
    {φ : B' →+* B} [hφ : φ.IsSmallExtension] : IsArtinianRing B' := sorry

/-- The target of a small extension is a local ring. -/
theorem isLocalRingTarget {B' : Type u} {B : Type v} [CommRing B'] [CommRing B]
    {φ : B' →+* B} [hφ : φ.IsSmallExtension] : IsLocalRing B := sorry

/-- The target of a small extension is an Artinian ring. -/
theorem isArtinianRingTarget {B' : Type u} {B : Type v} [CommRing B'] [CommRing B]
    {φ : B' →+* B} [hφ : φ.IsSmallExtension] : IsArtinianRing B := sorry

/-- A small extension is a local ring homomorphism. -/
instance instIsLocalHom {B' : Type u} {B : Type v} [CommRing B'] [CommRing B]
    (φ : B' →+* B) [φ.IsSmallExtension] : IsLocalHom φ := sorry

/-- The kernel of a small extension is a simple module over the source. -/
instance instKerIsSimpleModule {B' : Type u} {B : Type v} [CommRing B'] [CommRing B]
    (φ : B' →+* B) [φ.IsSmallExtension] : IsSimpleModule B' (RingHom.ker φ) := sorry

/-- The kernel of a small extension lies in the source maximal ideal. -/
theorem ker_le_maximalIdeal {B' : Type u} {B : Type v} [CommRing B'] [CommRing B]
    {φ : B' →+* B} [hφ : φ.IsSmallExtension] :
    RingHom.ker φ ≤ IsLocalRing.maximalIdeal B' := sorry

/-- The square of the kernel of a small extension vanishes. -/
theorem ker_sq_eq_bot {B' : Type u} {B : Type v} [CommRing B'] [CommRing B]
    {φ : B' →+* B} [hφ : φ.IsSmallExtension] : RingHom.ker φ ^ 2 = ⊥ := sorry

/-- The maximal ideal of the source of a small extension is nilpotent. -/
@[stacks 0DYG "small-extension source maximal ideal is nilpotent"]
theorem sourceMaximalIdeal_isNilpotent
    {B' : Type u} {B : Type v} [CommRing B'] [CommRing B]
    (φ : B' →+* B) [φ.IsSmallExtension] :
    IsNilpotent (IsLocalRing.maximalIdeal B') := sorry

end IsSmallExtension

/-- A surjective map from a local Artinian ring to a nontrivial ring whose kernel has length one
is a small extension. -/
theorem IsSmallExtension.of_surjective_of_ker_length
    {B' : Type u} {B : Type v} [CommRing B'] [CommRing B] (φ : B' →+* B)
    [IsLocalRing B'] [IsArtinianRing B'] [Nontrivial B]
    (h_surjective : Function.Surjective φ)
    (h_ker_length : Module.length B' (RingHom.ker φ) = 1) : φ.IsSmallExtension := sorry

end RingHom
