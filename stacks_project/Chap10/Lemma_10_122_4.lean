/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.QuasiFinite.Fiber
import StacksCheckRecall

/-!
# Quasi-finite fibres

@stack 0H8X

The zero-dimensional finite-type fibre criteria are canonical library data;
the numbered declaration keeps the source's three-way `List.TFAE` packaging.
-/

@[expose] public section

universe u v

open PrimeSpectrum
open Algebra.TensorProduct

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S]

/- Lemma 10.122.4 (0H8X): for a finite type ring map `R → S` and a prime
`p` of `R`, quasi-finiteness at every prime over `p`, finiteness of the fibre
algebra over `κ(p)`, and finiteness of the fibre spectrum are equivalent. -/
@[stacks 0H8X "source three-clause form"]
#check fun p : PrimeSpectrum R => show
  List.TFAE
    [ (∀ q : PrimeSpectrum S,
          PrimeSpectrum.comap (algebraMap R S) q = p → Algebra.QuasiFiniteAt R q.asIdeal)
    , Module.Finite p.asIdeal.ResidueField (p.asIdeal.Fiber S)
    , Finite (PrimeSpectrum (p.asIdeal.Fiber S))
    ] from Algebra.FiniteType.quasiFiniteAt_fiberTFAE p

/-! Canonical owners used by the source-facing TFAE. -/

@[stacks 0H8X "quasi-finiteness under base change"]
#check @Algebra.QuasiFiniteAt.baseChange

@[stacks 0H8X "fiber-prime equivalence"]
#check @PrimeSpectrum.preimageEquivFiber

@[stacks 0H8X "fiber-prime homeomorphism"]
#check @PrimeSpectrum.preimageHomeomorphFiber

@[stacks 0H8X "quasi-finiteness at the canonical fiber prime"]
#check @Algebra.QuasiFiniteAt.iff_fiberPrimeAt

end
