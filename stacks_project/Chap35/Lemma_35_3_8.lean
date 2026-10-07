module

public import ReasLib.Algebra.Module.DescentDatum.BaseChange
import StacksCheckRecall

@[expose] public section

open scoped TensorProduct

universe u

/- Lemma 35.3.8: if `R → A` and `R → R'` are faithfully flat and every
module descent datum for `R' → R' ⊗[R] A` is effective, then every module
descent datum for `R → A` is effective. -/
@[stacks 039X] #check (Module.DescentDatum.allEffective_of_baseChange :
  ∀ {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R']
    [Module.FaithfullyFlat R A] [Module.FaithfullyFlat R R'],
    (∀ (N' : Type u) [AddCommGroup N'] [Module R' N']
      [Module (R' ⊗[R] A) N'] [IsScalarTower R' (R' ⊗[R] A) N']
      [SMulCommClass R' (R' ⊗[R] A) N']
      (D' : Module.DescentDatum R' (R' ⊗[R] A) N'), D'.IsEffective) →
    ∀ (N : Type u) [AddCommGroup N] [Module R N] [Module A N]
      [IsScalarTower R A N] [SMulCommClass R A N]
      (D : Module.DescentDatum R A N), D.IsEffective)
