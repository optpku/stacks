/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Affine quasi-finite loci

This leaf connects the ring-theoretic predicate `Algebra.QuasiFiniteAt` with the pointwise
quasi-finite predicate on an affine scheme morphism.  The pointwise bridge is kept independent of
finite type; the open-locus theorem carries the finite-type assumption required by the source.

@stack 00QA
-/

@[expose] public section

open AlgebraicGeometry
open RingHom
open Topology

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S]

omit [Algebra.FiniteType R S] in
/-- At a prime `q` of `S`, the pointwise quasi-finite predicate of
`Spec.map (algebraMap R S)` is equivalent to `Algebra.QuasiFiniteAt R q.asIdeal`. -/
@[stacks 00QA "affine pointwise quasi-finite bridge"]
lemma specMap_quasiFiniteAt_iff (q : PrimeSpectrum S) :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))).QuasiFiniteAt q ↔
      Algebra.QuasiFiniteAt R q.asIdeal := sorry

/-- Lemma 10.123.13: for a finite-type ring map `R → S`, the quasi-finite locus in `Spec(S)` is
open. -/
@[stacks 00QA "affine quasi-finite locus open"]
theorem isOpen_setOf_quasiFiniteAt :
    IsOpen {q : PrimeSpectrum S | Algebra.QuasiFiniteAt R q.asIdeal} := sorry

end Scheme.Hom
end AlgebraicGeometry
