module

public import Mathlib.Algebra.Homology.LocalCohomology
public import Mathlib.Algebra.Regular.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import stacks_project.Chap58.Lemma_58_19_2
public import stacks_project.Chap58.Lemma_58_24_1

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.PuncturedSpectrum
open IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

/-- Lemma 58.24.2: in Situation 58.19.1, if `A` is `f`-adically complete, `f` is a
nonzerodivisor, `H¹_m(A ⧸ fA)` and `H²_m(A ⧸ fA)` are finite `A`-modules, and
purity holds at `(A_f)_p` for every maximal ideal `p` of `A_f`, then the restriction
functor `FÉt_U ⟶ FÉt_{U₀}` identified with
`Scheme.finiteEtaleBaseChange (principalQuotientMap f)` is essentially
surjective. -/
@[stacks 0EKA, instance]
instance finiteEtaleBaseChange_essSurj_of_complete_localCohomology_purity
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (f : maximalIdeal A)
    [IsAdicComplete (principalIdeal f) A]
    [Fact (IsRegular (f : A))]
    [Module.Finite A
      ((localCohomology (maximalIdeal A) 1).obj
        (ModuleCat.of A
          (A ⧸ (principalIdeal f • (⊤ : Submodule A A)))))]
    [Module.Finite A
      ((localCohomology (maximalIdeal A) 2).obj
        (ModuleCat.of A
          (A ⧸ (principalIdeal f • (⊤ : Submodule A A)))))]
    [Fact (hasPurityAtMaximalsAway f)] :
    (Scheme.finiteEtaleBaseChange (principalQuotientMap f)).EssSurj := sorry

end AlgebraicGeometry.PuncturedSpectrum
