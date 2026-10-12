/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.IndZariski.WLocal
import StacksCheckRecall

/-!
# Lemma 61.6.5

A ring map that identifies local rings, with w-local spectra and a w-local
spectrum map, is ind-Zariski.
-/

@[expose] public section

universe u

open PrimeSpectrum

/- Lemma 61.6.5: if `f : A →+* B` identifies local rings, `PrimeSpectrum A` and
`PrimeSpectrum B` are w-local, and `comap f` is w-local, then `f` is
ind-Zariski. -/
@[stacks 097F] #check (RingHom.IndZariski.of_isIsoOnLocalRings :
  ∀ {A B : Type u} [CommRing A] [CommRing B] {f : A →+* B}
    [WLocalSpace (PrimeSpectrum A)] [WLocalSpace (PrimeSpectrum B)]
    [IsWLocalMap (comap f)], f.IsIsoOnLocalRings → f.IndZariski)

/- Under the w-local hypotheses, a ring map is
ind-Zariski if and only if it identifies local rings. -/
#check (RingHom.IndZariski.isIsoOnLocalRings_iff :
  ∀ {A B : Type u} [CommRing A] [CommRing B] {f : A →+* B}
    [WLocalSpace (PrimeSpectrum A)] [WLocalSpace (PrimeSpectrum B)]
    [IsWLocalMap (comap f)], f.IndZariski ↔ f.IsIsoOnLocalRings)
