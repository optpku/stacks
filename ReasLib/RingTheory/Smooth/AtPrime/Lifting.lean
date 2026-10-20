/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.Tactic.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.AlgHom.Lifting
public import ReasLib.RingTheory.RingHom.Fiber.ResidueField
public import ReasLib.RingTheory.RingHom.Local.AtPrime
public import ReasLib.RingTheory.RingHom.SmallExtension
public import ReasLib.RingTheory.RingHom.SquareZero.Local
public import ReasLib.RingTheory.Smooth.AtPrime

@[expose] public section

/-!
# Infinitesimal lifting at a prime

This leaf owns the reusable local lifting predicates behind Stacks Lemma
10.141.2.  The extension map is an explicit `R`-algebra homomorphism; its
underlying ring homomorphism supplies the square-zero or small-extension
owner and the canonical target closed point.  Thus the predicates do not
silently require the base ring to be local and do not choose an ambient
`Algebra B' B` instance.

The converse criteria test rings in `Type (max u v)`, which contains the
localizations and quotients of finite polynomial presentations used in the
source proof. Forward implications allow arbitrary test universes, with
the same test universes on both sides of each implication.

@stack 02HT
-/

universe u v w x

namespace Algebra.IsSmoothAt

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- The square-zero local lifting condition at `q`.  The target point is the
canonical maximal point induced by the square-zero extension, which is the
same point as the local target maximal ideal in the source formulation.
-/
@[stacks 02HT "square-zero lifting criterion"]
def SquareZeroLifts (q : PrimeSpectrum S) : Prop :=
  ∀ {B' : Type w} {B : Type x} [CommRing B'] [CommRing B]
    [Algebra R B'] [Algebra R B] [IsLocalRing B']
    (π : B' →ₐ[R] B) [π.toRingHom.IsSquareZeroExtension]
    (f : S →ₐ[R] B),
    q = PrimeSpectrum.comap f.toRingHom
      (RingHom.IsSquareZeroExtension.targetClosedPoint π.toRingHom) →
      AlgHom.HasLift π f

/-- The small-extension local lifting condition at `q`.  Locality and the
Artinian hypotheses on the extension are supplied by
`RingHom.IsSmallExtension`; no theorem-produced target instance is installed
inside the predicate.
-/
@[stacks 02HT "small-extension lifting criterion"]
def SmallExtensionLifts (q : PrimeSpectrum S) : Prop :=
  ∀ {B' : Type w} {B : Type x} [CommRing B'] [CommRing B]
    [Algebra R B'] [Algebra R B]
    (π : B' →ₐ[R] B) [π.toRingHom.IsSmallExtension]
    (f : S →ₐ[R] B),
    q = PrimeSpectrum.comap f.toRingHom
      (RingHom.IsSquareZeroExtension.targetClosedPoint π.toRingHom) →
      AlgHom.HasLift π f

namespace SmallExtensionLifts

/-- The small-extension lifting condition with the additional residue-field
bijectivity requirement from Stacks Lemma 10.141.2 (4).

The residue-field map is formed at the extension's canonical target closed
point, with the displayed equality used to name its source as `q`.  Thus the
formal predicate is literally the map `κ(q) → κ(m)` in the source statement.
-/
@[stacks 02HT "small-extension residue-field lifting criterion"]
def withResidue (q : PrimeSpectrum S) : Prop :=
  ∀ {B' : Type w} {B : Type x} [CommRing B'] [CommRing B]
    [Algebra R B'] [Algebra R B]
    (π : B' →ₐ[R] B) [π.toRingHom.IsSmallExtension]
    (f : S →ₐ[R] B),
    (hq : q = PrimeSpectrum.comap f.toRingHom
      (RingHom.IsSquareZeroExtension.targetClosedPoint π.toRingHom)) →
    Function.Bijective
        (RingHom.ResidueField.mapAtSourcePrime f.toRingHom q
          (RingHom.IsSquareZeroExtension.targetClosedPoint π.toRingHom) hq) →
      AlgHom.HasLift π f

end SmallExtensionLifts

/-- Square-zero lifting implies small-extension lifting. -/
theorem SquareZeroLifts.toSmallExtension
    (q : PrimeSpectrum S)
    (h : SquareZeroLifts.{u, v, w, x} (R := R) (S := S) q) :
    SmallExtensionLifts.{u, v, w, x} (R := R) (S := S) q := sorry

/-- Smoothness at a prime supplies the square-zero lifting condition. -/
theorem hasSquareZeroLifts
    [IsNoetherianRing R] [Algebra.FiniteType R S]
    (q : PrimeSpectrum S) (h : Algebra.IsSmoothAt R q.asIdeal) :
    SquareZeroLifts.{u, v, w, x} (R := R) (S := S) q := sorry

/-- Under the Noetherian finite-type hypotheses, smoothness at `q` is exactly
the square-zero lifting condition.  This named equivalence is the preferred
downstream interface to the first clause of `lifting_tfae`. -/
@[stacks 02HT "smoothness and square-zero lifting"]
theorem iff_hasSquareZeroLifts
    [IsNoetherianRing R] [Algebra.FiniteType R S]
    (q : PrimeSpectrum S) :
    Algebra.IsSmoothAt R q.asIdeal ↔
      SquareZeroLifts.{u, v, max u v, max u v} (R := R) (S := S) q := sorry

/-- Adding a residue-field hypothesis does not change the lifting conclusion. -/
theorem SmallExtensionLifts.toWithResidue
    (q : PrimeSpectrum S)
    (h : SmallExtensionLifts.{u, v, w, x} (R := R) (S := S) q) :
    SmallExtensionLifts.withResidue.{u, v, w, x} (R := R) (S := S) q := sorry

/-- The square-zero and small-extension lifting conditions are equivalent
under the Noetherian finite-type hypotheses. -/
@[stacks 02HT "square-zero and small-extension lifting"]
theorem SquareZeroLifts.iff_smallExtensionLifts
    [IsNoetherianRing R] [Algebra.FiniteType R S]
    (q : PrimeSpectrum S) :
    SquareZeroLifts.{u, v, max u v, max u v} (R := R) (S := S) q ↔
      SmallExtensionLifts.{u, v, max u v, max u v} (R := R) (S := S) q := sorry

/-- The small-extension condition is equivalent to its residue-field
specialization under the Noetherian finite-type hypotheses. -/
@[stacks 02HT "small-extension and residue-field lifting"]
theorem SmallExtensionLifts.iff_withResidue
    [IsNoetherianRing R] [Algebra.FiniteType R S]
    (q : PrimeSpectrum S) :
    SmallExtensionLifts.{u, v, max u v, max u v} (R := R) (S := S) q ↔
      SmallExtensionLifts.withResidue.{u, v, max u v, max u v}
        (R := R) (S := S) q := sorry

/-- The converse direction of the local infinitesimal criterion under the
Noetherian finite-type hypotheses. -/
theorem of_withResidue
    [IsNoetherianRing R] [Algebra.FiniteType R S]
    (q : PrimeSpectrum S)
    (h : SmallExtensionLifts.withResidue.{u, v, max u v, max u v}
      (R := R) (S := S) q) :
    Algebra.IsSmoothAt R q.asIdeal := sorry

/-- Lemma 10.141.2 (Stacks tag `02HT`): for a Noetherian finite-type algebra,
smoothness at `q` is equivalent to the square-zero lifting criterion, the
small-extension criterion, and the small-extension criterion with a
bijective residue-field map. -/
@[stacks 02HT]
theorem lifting_tfae
    [IsNoetherianRing R] [Algebra.FiniteType R S]
    (q : PrimeSpectrum S) :
    List.TFAE
      [ Algebra.IsSmoothAt R q.asIdeal
      , SquareZeroLifts.{u, v, max u v, max u v} (R := R) (S := S) q
      , SmallExtensionLifts.{u, v, max u v, max u v} (R := R) (S := S) q
      , SmallExtensionLifts.withResidue.{u, v, max u v, max u v}
          (R := R) (S := S) q ] := sorry

end

end Algebra.IsSmoothAt
