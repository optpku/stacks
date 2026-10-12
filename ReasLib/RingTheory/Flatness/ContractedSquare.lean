/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Flatness.Nilpotent

/-!
# Flatness at a Contracted Extended Square

This leaf owns the flatness comparison obtained by contracting the square of
an extended ideal. The contracted ideal is kept as the standard
`Ideal.comap`/`Ideal.map` expression rather than introducing a second ideal
operation for one use case.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Module.Flat.ContractedSquare

variable {R : Type u} {R' : Type v} [CommRing R] [CommRing R'] [Algebra R R']
variable {M : Type w} [AddCommGroup M] [Module R M]

/-- Stacks `051I`: quotient flatness modulo `I` and flatness after base change
imply quotient flatness modulo the contraction of the square of the extended
ideal. -/
@[stacks 051I]
theorem of_quotient_flat_of_baseChange {I : Ideal R}
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))))
    (hbase : Module.Flat R' (R' ⊗[R] M)) :
    Module.Flat
      (R ⧸ Ideal.comap (algebraMap R R') (Ideal.map (algebraMap R R') (I ^ 2)))
      (M ⧸ ((Ideal.comap (algebraMap R R')
        (Ideal.map (algebraMap R R') (I ^ 2))) • (⊤ : Submodule R M))) := sorry

end Module.Flat.ContractedSquare
