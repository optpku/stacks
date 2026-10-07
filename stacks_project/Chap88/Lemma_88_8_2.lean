module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap88.Definition_88_20_1_Ring
public import stacks_project.Chap88.Lemma_88_8_2_Jacobian

/-!
# Characterization of rig-étale algebras

Lemma 88.8.2 equates rig-étaleness of an object of `C'` with vanishing of
`I ^ c` on the completed naive cotangent complex in `D(B)`, annihilation of
its homology, the same annihilation for every stage complex, Artin relation
generators, elementary square Jacobian minors, and Fitting containments of
the completed Jacobian and Cramer ideals.
-/

@[expose] public section

universe u

open Algebra.NaiveCotangent.Adic

/-- Lemma 88.8.2: for a Noetherian ring `A`, an ideal `I`, and an algebra `B`
topologically of finite type over `(A, I)`, equipped with a finite completed
presentation `P` and completed naive cotangent complex `naiveCotangent I P`,
the following are equivalent: `B` is `RigEtale` over `(A, I)`; some `I ^ c`
acts by zero on `naiveCotangentObject I P` in `D(B)`; `I ^ c` annihilates
homology of `naiveCotangent I P` in degrees `1` and `0`; the same annihilation
holds for every stage complex `stageComplex I P n`; every `a ∈ I` has a power
killing homological degree zero with `r` kernel elements satisfying the
relation condition; every `a ∈ I` is elementary for a square completed
Jacobian minor after raising to a power; and some `I ^ c` is contained in both
the Jacobian ideal and the Cramer ideal of `P`. -/
@[stacks 0AJU]
theorem Algebra.RigEtale.tfae {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B]
    [TopologicallyFiniteType I B] {ι : Type u} [Fintype ι]
    (P : NaiveCotangent.Adic.Presentation A B I ι) :
    List.TFAE
      [RigEtale I B,
        ∃ c : ℕ, P.powSmulIdEqZero c,
        ∃ c : ℕ, P.homologyAnnihilated c,
        ∃ c : ℕ, P.stageHomologyAnnihilated c,
        P.existsRelationGenerators,
        P.existsElementarySquare,
        P.fittingContainsPow] :=
  sorry
