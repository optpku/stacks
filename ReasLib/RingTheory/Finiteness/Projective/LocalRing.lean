/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Finiteness.Projective

/-!
# Finite Projective Modules over Local Rings

This leaf isolates the elementary local-ring criterion. The flat-local-hom
specialization of faithfully-flat descent lives in `Projective.FlatLocal`.
-/

@[expose] public section

universe u v

namespace Module.FiniteProjective

section LocalRing

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- A finite flat module over a local ring is finite projective. -/
@[stacks 00NZ "finite flat modules over local rings are finite projective"]
theorem of_finite_flat_of_localRing [IsLocalRing R]
    (hfinite : Module.Finite R M) (hflat : Module.Flat R M) :
    Module.FiniteProjective R M := by
  letI := hfinite
  letI := hflat
  letI : Module.Free R M := Module.free_of_flat_of_isLocalRing
  exact ⟨hfinite, inferInstance⟩

/-- A finite-projective module over a local ring is free.

This is the explicit-proof companion to the local freeness theorem. It keeps finite projectivity
as a proposition argument, so callers do not need to install temporary finite, projective, or flat
instances merely to obtain the free module structure. -/
@[stacks 00JJ "(1) finite projective modules over local rings are free"]
theorem free_of_isLocalRing [IsLocalRing R]
    (hM : Module.FiniteProjective R M) : Module.Free R M := by
  letI := hM.finite
  letI := hM.projective
  exact Module.free_of_flat_of_isLocalRing

end LocalRing

end Module.FiniteProjective
