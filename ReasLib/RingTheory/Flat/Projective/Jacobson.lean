/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Flat.Projective
public import ReasLib.RingTheory.Jacobson.Ideal

@[expose] public section

/-!
# Lifting finite projectivity across Jacobson quotients

@stack 0D48
-/

universe u v

namespace Module.Projective

variable {R : Type u} [CommRing R]
variable {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Lemma 15.3.4, tag `0D48`: a finite flat module is projective when its
reduction modulo an ideal in the Jacobson radical is projective. -/
@[stacks 0D48]
theorem of_quotient_of_le_jacobson
    [Module.Finite R M] [Module.Flat R M]
    (hI : I ≤ Ring.jacobson R)
    (hquot : Module.Projective (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M))) :
    Module.Projective R M := sorry

end Module.Projective
