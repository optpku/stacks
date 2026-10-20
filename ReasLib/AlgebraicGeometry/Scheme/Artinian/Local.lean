module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Spectra of local Artinian rings

A scheme is the spectrum of a local Artinian ring when it is affine and its ring of
global sections is a local Artinian ring.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A scheme is the spectrum of a local Artinian ring when it is affine and
`Γ(X, ⊤)` is a local Artinian ring. -/
class IsSpecLocalArtinian (X : Scheme.{u}) : Prop extends IsAffine X where
  /-- Global sections form an Artinian ring. -/
  [isArtinianRing_Γ : IsArtinianRing Γ(X, ⊤)]
  /-- Global sections form a local ring. -/
  [isLocalRing_Γ : IsLocalRing Γ(X, ⊤)]

attribute [instance] IsSpecLocalArtinian.isArtinianRing_Γ
attribute [instance] IsSpecLocalArtinian.isLocalRing_Γ

/-- The spectrum of a local Artinian ring is a spectrum of a local Artinian ring. -/
instance instIsSpecLocalArtinianSpec {A : Type u} [CommRing A] [IsLocalRing A]
    [IsArtinianRing A] : IsSpecLocalArtinian (Spec (CommRingCat.of A)) := sorry

/-- `IsSpecLocalArtinian X` is equivalent to affinity together with `Γ(X, ⊤)` being
a local Artinian ring. -/
theorem isSpecLocalArtinian_iff {X : Scheme.{u}} :
    IsSpecLocalArtinian X ↔
      IsAffine X ∧ IsArtinianRing Γ(X, ⊤) ∧ IsLocalRing Γ(X, ⊤) := sorry

/-- A scheme is a spectrum of a local Artinian ring if and only if it is isomorphic
to `Spec A` for some local Artinian ring `A`. -/
theorem isSpecLocalArtinian_iff_exists_iso {X : Scheme.{u}} :
    IsSpecLocalArtinian X ↔
      ∃ (A : Type u) (_ : CommRing A) (_ : IsLocalRing A) (_ : IsArtinianRing A),
        Nonempty (X ≅ Spec (CommRingCat.of A)) := sorry

/-- In a pushout of spectra of local Artinian rings over a scheme, a closed immersion
from the common source induces a closed immersion into the pushout. -/
theorem Scheme.Pushout.fromY_isClosedImmersion_of_isSpecLocalArtinian {S : Scheme.{u}}
    {X X' Y Y' : Over S}
    [IsSpecLocalArtinian X.left] [IsSpecLocalArtinian X'.left]
    [IsSpecLocalArtinian Y.left] [IsSpecLocalArtinian Y'.left]
    {toX' : X ⟶ X'} {toY : X ⟶ Y}
    {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
    (h : IsPushout toX' toY fromX' fromY)
    [IsClosedImmersion toX'.left] :
    IsClosedImmersion fromY.left := sorry


/-- A spectrum of a local Artinian ring is a locally Noetherian scheme. -/
instance instIsLocallyNoetherian_of_isSpecLocalArtinian (X : Scheme.{u})
    [IsSpecLocalArtinian X] : IsLocallyNoetherian X := sorry


end AlgebraicGeometry
