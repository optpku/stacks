module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.FiniteEtaleNeighborhood
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

/- Lemma 58.23.2: in Situation 58.19.1, if `A` is `f`-adically complete, `f` is a
nonzerodivisor, and `H¹_m(A ⧸ fA)` and `H²_m(A ⧸ fA)` are finite `A`-modules, then
the restriction functor `colim_{U0 ⊂ U' ⊂ U} FÉt_{U'} ⟶ FÉt_{U0}` is an
equivalence. Here
`U = PuncturedSpectrum.scheme A`,
and `U0 = PuncturedSpectrum.scheme (A ⧸ Ideal.span {(f : A)})` are the punctured
spectra of `A` and `A/(f)`, respectively. -/
@[stacks 0BLV] #check
  (AlgebraicGeometry.PuncturedSpectrum.principalNeighborhoodRestriction_isEquivalence :
  ∀
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (f : maximalIdeal A)
    [IsAdicComplete (Ideal.span {(f : A)}) A]
    [Fact (IsRegular (f : A))]
    [Module.Finite A
      ((localCohomology (maximalIdeal A) 1).obj
        (ModuleCat.of A (A ⧸ Ideal.span {(f : A)})))]
    [Module.Finite A
      ((localCohomology (maximalIdeal A) 2).obj
        (ModuleCat.of A (A ⧸ Ideal.span {(f : A)})))]
    (t : ColimitCocone
      (Scheme.finiteEtaleNeighborhoodDiagram (principalQuotientMap f).ker)),
    Functor.IsEquivalence (principalNeighborhoodRestriction f t))

end AlgebraicGeometry.PuncturedSpectrum
