module

public import ReasLib.RingTheory.Flatness.ContractedSquare
import StacksCheckRecall

/-!
# Flatness over a contracted square ideal

@stack 051I
-/

@[expose] public section

open scoped TensorProduct

universe u v w

section

variable {R : Type u} {R' : Type v} [CommRing R] [CommRing R'] [Algebra R R']
variable {M : Type w} [AddCommGroup M] [Module R M]

/-
Lemma 10.101.4 (051I): if `M / IM` is flat over `R / I` and the base change
`R' ⊗[R] M` is flat over `R'`, then `M / I₂M` is flat over `R / I₂`, where
`I₂ = Ideal.comap (algebraMap R R') (Ideal.map (algebraMap R R') (I ^ 2))`.

The reusable owner is
`Module.Flat.ContractedSquare.of_quotient_flat_of_baseChange`; its namespace
records the mathematical construction, while this file remains the tagged
source-facing recall.
-/
@[stacks 051I]
#check (Module.Flat.ContractedSquare.of_quotient_flat_of_baseChange :
  ∀ {I : Ideal R},
    Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) →
    Module.Flat R' (R' ⊗[R] M) →
    Module.Flat
      (R ⧸ Ideal.comap (algebraMap R R') (Ideal.map (algebraMap R R') (I ^ 2)))
      (M ⧸ ((Ideal.comap (algebraMap R R')
        (Ideal.map (algebraMap R R') (I ^ 2))) • (⊤ : Submodule R M))))

end
