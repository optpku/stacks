module

public import ReasLib.RingTheory.Filtration.ArtinRees.LinearMap
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Flat base change for Artin-Rees bounds

@stack 07VG

An Artin-Rees bound is unchanged by flat extension of scalars.  The reusable theorem is stated
without finiteness assumptions; a companion retains the finite Noetherian setup of the source.
-/

open scoped Pointwise

universe u v w x

variable {A : Type u} {B : Type x} [CommRing A] [CommRing B]
variable [Algebra A B] [Module.Flat A B]
variable {M : Type v} {N : Type w}
variable [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

namespace LinearMap.IsArtinReesBound

/-- Flat extension of scalars preserves an Artin-Rees bound and its constant. -/
theorem baseChange {f : M →ₗ[A] N} {I : Ideal A} {c : ℕ}
    (hc : f.IsArtinReesBound I c) :
    (f.baseChange B).IsArtinReesBound (I.map (algebraMap A B)) c := sorry

section Source

variable [hA : IsNoetherianRing A] [hB : IsNoetherianRing B]
variable [hM : Module.Finite A M] [hN : Module.Finite A N]

include hA hB hM hN in
/-- Lemma 15.4.3: for a flat map of Noetherian rings and finite source and target modules, the
same Artin-Rees constant works after base change. -/
@[stacks 07VG]
theorem baseChange_of_finite {f : M →ₗ[A] N} {I : Ideal A} {c : ℕ}
    (hc : f.IsArtinReesBound I c) :
    (f.baseChange B).IsArtinReesBound (I.map (algebraMap A B)) c := sorry

end Source

end LinearMap.IsArtinReesBound
