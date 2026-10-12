/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Length
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Length after localization

@stack 00IZ

This leaf records the monotonicity of module length under localization. The statement uses the
canonical `LocalizedModule` owner and does not expose the Galois-insertion proof machinery.
-/

@[expose] public section

universe u v

variable {R : Type u} [CommRing R]
variable (S : Submonoid R)
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Lemma 10.52.7 (Tag 00IZ): localizing a module at a submonoid cannot increase its length. -/
@[stacks 00IZ]
theorem length_localizedModule_le :
    Module.length (Localization S) (LocalizedModule S M) ≤ Module.length R M := sorry
