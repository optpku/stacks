/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Filtration.ArtinRees.LinearMap
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Perturbing exact complexes under Artin-Rees bounds

@stack 07VE

Sufficiently high-order perturbations preserve an Artin-Rees bound, and over a finite module with
the ideal in the Jacobson radical they preserve exactness.
-/

open scoped Pointwise
open LinearMap

universe u v w x

variable {A : Type u} [CommRing A]
variable {L : Type v} [AddCommGroup L] [Module A L]
variable {M : Type w} [AddCommGroup M] [Module A M]
variable {N : Type x} [AddCommGroup N] [Module A N]
variable {I : Ideal A} {c : ℕ}
variable {f f' : L →ₗ[A] M} {g g' : M →ₗ[A] N}

namespace LinearMap.IsArtinReesBound

/-- An exact complex retains the Artin-Rees bound on its second map after a compatible
perturbation modulo `I ^ (c + 1)`. -/
@[stacks 07VE "Artin-Rees bound under perturbation"]
theorem of_exact_of_congr_mod_pow
    (hf : f.IsArtinReesBound I c) (hg : g.IsArtinReesBound I c)
    (hexact : Function.Exact f g)
    (hff' : range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    (hgg' : range (g' - g) ≤ I ^ (c + 1) • (⊤ : Submodule A N))
    (hcomplex' : g'.comp f' = 0) :
    g'.IsArtinReesBound I c := sorry

end LinearMap.IsArtinReesBound

namespace Function.Exact

/-- A sufficiently high-order perturbation of an exact complex remains exact when its middle
module is finite and the controlling ideal lies in the Jacobson radical. -/
@[stacks 07VE "exactness under Artin-Rees perturbation"]
theorem of_congr_mod_pow_and_artinRees
    [IsNoetherianRing A] [Module.Finite A M]
    (hf : f.IsArtinReesBound I c) (hg : g.IsArtinReesBound I c)
    (hexact : Function.Exact f g)
    (hff' : range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    (hgg' : range (g' - g) ≤ I ^ (c + 1) • (⊤ : Submodule A N))
    (hI : I ≤ Ring.jacobson A) (hcomplex' : g'.comp f' = 0) :
    Function.Exact f' g' := sorry

end Function.Exact

section Source

variable [hA : IsNoetherianRing A]
variable [hL : Module.Finite A L] [hM : Module.Finite A M] [hN : Module.Finite A N]

include hA hL hM hN in
/-- Lemma 15.4.1 (1): under the finite Noetherian setup of the source, the same constant `c`
works in Artin-Rees for the perturbed second map `g'`. -/
@[stacks 07VE "(1), perturbed Artin-Rees bound"]
theorem LinearMap.IsArtinReesBound.perturb_of_finite_exact
    (hf : f.IsArtinReesBound I c) (hg : g.IsArtinReesBound I c)
    (hexact : Function.Exact f g)
    (hff' : range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    (hgg' : range (g' - g) ≤ I ^ (c + 1) • (⊤ : Submodule A N))
    (hI : I ≤ Ring.jacobson A) (hcomplex' : g'.comp f' = 0) :
    g'.IsArtinReesBound I c := sorry

include hA hL hM hN in
/-- Lemma 15.4.1 (2): under the finite Noetherian setup of the source, the perturbed complex
`L ⟶ M ⟶ N` remains exact. -/
@[stacks 07VE "(2), exact perturbed complex"]
theorem Function.Exact.perturb_of_finite_artinRees
    (hf : f.IsArtinReesBound I c) (hg : g.IsArtinReesBound I c)
    (hexact : Function.Exact f g)
    (hff' : range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    (hgg' : range (g' - g) ≤ I ^ (c + 1) • (⊤ : Submodule A N))
    (hI : I ≤ Ring.jacobson A) (hcomplex' : g'.comp f' = 0) :
    Function.Exact f' g' := sorry

end Source
