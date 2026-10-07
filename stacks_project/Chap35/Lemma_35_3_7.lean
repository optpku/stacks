module

public import ReasLib.Algebra.Module.DescentDatum.Reconstruction
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.3.7: a module descent datum along a faithfully flat ring map is
effective if and only if its canonical reconstruction map
`A ⊗[R] H⁰(D) ⟶ N` is an isomorphism. -/
@[stacks 039W] #check (@Module.DescentDatum.isEffective_iff_isIso_reconstruction :
  ∀ (R A N : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup N] [Module R N] [Module A N]
    [IsScalarTower R A N] [SMulCommClass R A N] [Module.FaithfullyFlat R A]
    (D : Module.DescentDatum R A N),
    D.IsEffective ↔ CategoryTheory.IsIso D.reconstruction)
