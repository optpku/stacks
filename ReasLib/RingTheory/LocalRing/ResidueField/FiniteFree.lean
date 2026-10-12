/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import ReasLib.RingTheory.LocalRing.ResidueField.Map
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Finite-free realizations of residue-field extensions

This leaf records the reusable existence theorem that realizes a finite
extension of a prime residue field by the residue field of the extended prime
in a finite free algebra.

@stack 07NE
-/

universe u v

namespace Ideal.ResidueField

variable {R : Type u} [CommRing R]

/-- Lemma 10.159.3: a finite extension of `p.ResidueField` is realized by the residue field at the
extended prime in a finite free `R`-algebra. -/
@[stacks 07NE "finite-free realization of a residue-field extension"]
theorem exists_finiteFree_realization
    (p : Ideal R) [p.IsPrime] (L : Type v) [Field L] [Algebra p.ResidueField L]
    [FiniteDimensional p.ResidueField L] :
    ∃ (S : Type (max u v)) (_ : CommRing S) (_ : Algebra R S) (_ : Module.Free R S)
      (_ : Module.Finite R S),
      let q : Ideal S := p.map (algebraMap R S)
      ∃ (hq : q.IsPrime) (hqp : q.LiesOver p),
        letI : q.IsPrime := hq
        letI : q.LiesOver p := hqp
        letI : Algebra p.ResidueField q.ResidueField :=
          Ideal.ResidueField.algebraOfLiesOver p q
        Nonempty (q.ResidueField ≃ₐ[p.ResidueField] L) := sorry

end Ideal.ResidueField
