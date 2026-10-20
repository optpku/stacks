module

public import ReasLib.RingTheory.RingHom.LiftingSquare
public import ReasLib.RingTheory.RingHom.SmallExtension
public import ReasLib.RingTheory.RingHom.SquareZero.Local
public import ReasLib.RingTheory.Smooth.Adic.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Local lifting criteria for maximal-ideal-adic formal smoothness

The reusable predicates in this file express infinitesimal lifting through
commutative squares.  Closed points and residue-field maps are taken from the
extension map itself, so the public statements require no theorem-produced
local instances on target rings.

@stack 0DYG
-/

universe u v w x

namespace RingHom.MaximalIdealAdic

/-- The square-zero lifting property for a local ring map, tested against
local square-zero sources with nilpotent maximal ideal and unchanged residue
field. -/
@[stacks 0DYG "maximal-ideal-adic square-zero lifting property"]
def HasSquareZeroLifts {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) : Prop :=
  ∀ {A' : Type w} {A : Type x} [CommRing A'] [CommRing A] [IsLocalRing A']
    (π : A' →+* A) [π.IsSquareZeroExtension]
    (_ : IsNilpotent (IsLocalRing.maximalIdeal A'))
    (sq : RingHom.LiftingSquare f π)
    (hclosed : RingHom.IsSquareZeroExtension.IsLocalAtClosedPoint π sq.lower)
    (_ : Function.Bijective
      (RingHom.IsSquareZeroExtension.residueFieldMap π sq.lower hclosed)),
      sq.HasLift

/-- The small-extension lifting property for a local ring map, with unchanged
residue field at the distinguished closed point. -/
@[stacks 0DYG "maximal-ideal-adic small-extension lifting property"]
def HasSmallExtensionLifts {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) : Prop :=
  ∀ {A' : Type w} {A : Type x} [CommRing A'] [CommRing A]
    (π : A' →+* A) [π.IsSmallExtension]
    (sq : RingHom.LiftingSquare f π)
    (hclosed : RingHom.IsSquareZeroExtension.IsLocalAtClosedPoint π sq.lower)
    (_ : Function.Bijective
      (RingHom.IsSquareZeroExtension.residueFieldMap π sq.lower hclosed)),
      sq.HasLift

/-- The square-zero lifting property implies the corresponding property for
small extensions. -/
theorem HasSquareZeroLifts.hasSmallExtensionLifts
    {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    {f : R →+* S} (h : HasSquareZeroLifts.{u, v, w, x} f) :
    HasSmallExtensionLifts.{u, v, w, x} f := sorry

/-- For a local map with Noetherian target, lifting against small extensions
implies lifting against all admissible square-zero extensions. -/
theorem hasSquareZeroLifts_of_hasSmallExtensionLifts
    {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] [IsNoetherianRing S]
    (h : HasSmallExtensionLifts.{u, v, w, x} f) :
    HasSquareZeroLifts.{u, v, w, x} f := sorry

/-- Lemma 15.38.1, equivalence (1)-(2), tag `0DYG`: a local homomorphism is formally smooth for
the target maximal-ideal-adic topology exactly when it has the admissible square-zero lifting
property. -/
@[stacks 0DYG "Lemma 15.38.1, equivalence (1)-(2): square-zero local lifts"]
theorem formallySmooth_iff_hasSquareZeroLifts
    {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] :
    f.formally_smooth_for_adic (IsLocalRing.maximalIdeal S) ↔
      HasSquareZeroLifts.{u, v, max u v, max u v} f := sorry

/-- Lemma 15.38.1, equivalence (1)-(3), tag `0DYG`: for a local homomorphism with Noetherian
target, maximal-ideal-adic formal smoothness can be tested only against small extensions with
unchanged residue field. -/
@[stacks 0DYG "Lemma 15.38.1, equivalence (1)-(3): small-extension local lifts"]
theorem formallySmooth_iff_hasSmallExtensionLifts
    {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] [IsNoetherianRing S] :
    f.formally_smooth_for_adic (IsLocalRing.maximalIdeal S) ↔
      HasSmallExtensionLifts.{u, v, max u v, max u v} f := sorry

end RingHom.MaximalIdealAdic
