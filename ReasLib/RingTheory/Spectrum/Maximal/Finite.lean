/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.RingHom.QuasiFinite
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Spectrum.Maximal.Over

/-!
# Finite maximal spectra of finite semilocal algebras

The local-ring theorem `MaximalSpectrum.finite_of_moduleFinite` handles a
single closed point.  This leaf gives the corresponding semilocal statement,
which is the natural reusable owner for finite intermediate overrings.
-/

@[expose] public section

universe u v

namespace MaximalSpectrum

/-- Tag `00PC`: a module-finite algebra over a ring with finitely many maximal
ideals has finitely many maximal ideals.  The finite base spectrum is an
explicit hypothesis rather than a global instance, because the base algebra
is not recoverable from the target type alone. -/
@[stacks 00PC "finite maximal spectrum of a finite semilocal algebra"]
theorem finite_of_moduleFinite_of_semilocal
    (R : Type u) {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Finite (MaximalSpectrum R)] [Module.Finite R S] :
    Finite (MaximalSpectrum S) := sorry

end MaximalSpectrum
