module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.RingTheory.AdicCompletion.RigSmooth

/-!
# Lifting maps along a principal adic filtration with torsion cutoff
-/

@[expose] public section

universe u

namespace Algebra.NaiveCotangent.Adic

/-- Let `I = (a)` be a principal ideal of a Noetherian ring `A`, and let `B`
be a topologically finite type `A`-algebra for the `I`-adic topology. Suppose
`a^c` annihilates `Ext¹_B(NL_{B/A}^∧, N)` for every `B`-module `N`, and `C` is
an `I`-adically complete `A`-algebra with `C[a^∞] ∩ a^d C = 0`. If
`n > max (2c, c + d)`, every `A`-algebra map `B → C/a^n C` agrees modulo
`a^{n-c} C` with an `A`-algebra map `B → C`. -/
theorem exists_hom_of_powerTorsion_disjoint {A B C : Type u}
    [CommRing A] [IsNoetherianRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] {I : Ideal A} {a : A} (hI : I = Ideal.span {a})
    [Algebra.TopologicallyFiniteType I B] (c : ℕ)
    (hann : Algebra.annihilatesExt1NaiveCotangent I B c)
    [IsAdicComplete (I.map (algebraMap A C)) C] (d : ℕ)
    (hd : Submodule.torsion' C C (Submonoid.powers (algebraMap A C a)) ⊓
        (I.map (algebraMap A C)) ^ d = ⊥)
    {n : ℕ} (hn : max (2 * c) (c + d) < n)
    (ψn : B →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ n) :
    ∃ φ : B →ₐ[A] C,
      (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right (Nat.sub_le n c))).comp ψn =
        (Ideal.Quotient.mkₐ A ((I.map (algebraMap A C)) ^ (n - c))).comp φ :=
  sorry

end Algebra.NaiveCotangent.Adic
