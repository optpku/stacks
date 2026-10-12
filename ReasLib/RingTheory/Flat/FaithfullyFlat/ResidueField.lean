/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.LocalRing.ResidueField.MaximalIdeal

/-!
# Faithful flatness detected by residue-field fibers

This leaf places the fiberwise criteria on `Module.FaithfullyFlat`, while the
maximal-ideal tensor/quotient comparison remains owned by
`Ideal.ResidueField`.

@stack 00HP
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Module.FaithfullyFlat

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Stacks `00HP`: a flat module is faithfully flat exactly when every
maximal-ideal residue-field tensor fiber is nontrivial. -/
@[stacks 00HP "faithful flatness by maximal residue-field fibers"]
theorem iff_forall_nontrivial_tensor_residueField [Module.Flat R M] :
    Module.FaithfullyFlat R M ↔
      ∀ (I : Ideal R) (_ : I.IsMaximal), Nontrivial (M ⊗[R] I.ResidueField) := sorry

/-- Stacks `00HP`: a flat module is faithfully flat exactly when every
prime residue-field tensor fiber is nontrivial. -/
@[stacks 00HP "faithful flatness by prime residue-field fibers"]
theorem iff_forall_nontrivial_tensor_primeResidueField [Module.Flat R M] :
    Module.FaithfullyFlat R M ↔
      ∀ p : PrimeSpectrum R, Nontrivial (M ⊗[R] p.asIdeal.ResidueField) := sorry

/-- Lemma 10.39.15 (Stacks `00HP`): for a flat module, faithful flatness,
tensor-faithfulness, and nontriviality of all prime or maximal residue-field
fibers form a canonical `List.TFAE`. -/
@[stacks 00HP]
theorem tfae_nontrivial_tensor_residueField [Module.Flat R M] :
    List.TFAE
      [Module.FaithfullyFlat R M,
        ∀ (N : Type (max u v)) [AddCommGroup N] [Module R N],
          Nontrivial N → Nontrivial (M ⊗[R] N),
        ∀ p : PrimeSpectrum R, Nontrivial (M ⊗[R] p.asIdeal.ResidueField),
        ∀ (I : Ideal R) (_ : I.IsMaximal), Nontrivial (M ⊗[R] I.ResidueField)] := sorry

end Module.FaithfullyFlat
