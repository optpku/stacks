/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ExactSequence
public import ReasLib.LinearAlgebra.UniversallyInjective.Quotient

@[expose] public section

/-!
@stack 00MI

# Exactness of finite complexes from the closed fiber

The displayed finite complexes are organized by the canonical
`CategoryTheory.ComposableArrows` owner.  Exactness at the left endpoint is stated separately as
injectivity of the leftmost differential, because the displayed row begins with a zero object but
does not end with one.
-/

open CategoryTheory IsLocalRing

universe u v

namespace CriteriaForFlatness

section Sequence

variable {S : Type u} [CommRing S]
variable {n : ℕ} {F : Fin (n + 2) → Type v}
variable [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]

/-- The arrow in the reversed finite row corresponding to a displayed differential
`F (i + 1) → F i`. -/
noncomputable def finiteSequenceMap
    (d : ∀ i : Fin (n + 1), F i.succ →ₗ[S] F i.castSucc) (i : Fin (n + 1)) :
    ModuleCat.of S (F i.castSucc.rev) ⟶ ModuleCat.of S (F i.succ.rev) :=
  eqToHom (congrArg (fun j ↦ ModuleCat.of S (F j)) (Fin.rev_castSucc i)) ≫
    ModuleCat.ofHom (d i.rev) ≫
    eqToHom (congrArg (fun j ↦ ModuleCat.of S (F j)) (Fin.rev_succ i).symm)

/-- The canonical composable row `F (n + 1) ⟶ ⋯ ⟶ F 0` associated to the displayed
differentials. -/
noncomputable def finiteSequence
    (d : ∀ i : Fin (n + 1), F i.succ →ₗ[S] F i.castSucc) :
    ComposableArrows (ModuleCat S) (n + 1) :=
  ComposableArrows.mkOfObjOfMapSucc
    (fun i ↦ ModuleCat.of S (F i.rev)) (finiteSequenceMap d)

end Sequence

section Reduction

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]
variable {n : ℕ} {F : Fin (n + 2) → Type v}
variable [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
variable [∀ i, IsScalarTower R S (F i)]

/-- The arrow induced on quotients by `maximalIdeal R` from a displayed differential. -/
noncomputable def reducedFiniteSequenceMap
    (d : ∀ i : Fin (n + 1), F i.succ →ₗ[S] F i.castSucc) (i : Fin (n + 1)) :
    ModuleCat.of R
        (F i.castSucc.rev ⧸ maximalIdeal R • (⊤ : Submodule R (F i.castSucc.rev))) ⟶
      ModuleCat.of R
        (F i.succ.rev ⧸ maximalIdeal R • (⊤ : Submodule R (F i.succ.rev))) :=
  eqToHom
      (congrArg
        (fun j ↦ ModuleCat.of R (F j ⧸ maximalIdeal R • (⊤ : Submodule R (F j))))
        (Fin.rev_castSucc i)) ≫
    ModuleCat.ofHom
      (((d i.rev).restrictScalars R).quotientMapByIdeal (maximalIdeal R)) ≫
    eqToHom
      (congrArg
        (fun j ↦ ModuleCat.of R (F j ⧸ maximalIdeal R • (⊤ : Submodule R (F j))))
        (Fin.rev_succ i).symm)

variable (R) in
/-- The composable row obtained from `finiteSequence d` by reducing every term and
differential modulo `maximalIdeal R`. -/
noncomputable def reducedFiniteSequence
    (d : ∀ i : Fin (n + 1), F i.succ →ₗ[S] F i.castSucc) :
    ComposableArrows (ModuleCat R) (n + 1) :=
  ComposableArrows.mkOfObjOfMapSucc
    (fun i ↦
      ModuleCat.of R (F i.rev ⧸ maximalIdeal R • (⊤ : Submodule R (F i.rev))))
    (reducedFiniteSequenceMap d)

end Reduction

end CriteriaForFlatness

/-- Lemma 10.99.5 (1): let `R → S` be a local homomorphism of local Noetherian rings.
If `0 → F (n + 1) → ⋯ → F 0` is a finite complex of finite `S`-modules which are flat over
`R`, and its reduction modulo `maximalIdeal R` is exact, then the original complex is exact. -/
@[stacks 00MI]
theorem finiteComplexExact_of_reducedFiniteComplexExact
    {R : Type u} {S : Type v} {n : ℕ} {F : Fin (n + 2) → Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [IsNoetherianRing R] [IsNoetherianRing S]
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    (d : ∀ i : Fin (n + 1), F i.succ →ₗ[S] F i.castSucc)
    (hfinite : ∀ i, Module.Finite S (F i)) (hflat : ∀ i, Module.Flat R (F i))
    (hcomplex : (CriteriaForFlatness.finiteSequence d).IsComplex)
    (hexact_mod :
      Function.Injective
          (((d (Fin.last n)).restrictScalars R).quotientMapByIdeal (maximalIdeal R)) ∧
        (CriteriaForFlatness.reducedFiniteSequence R d).Exact) :
    Function.Injective (d (Fin.last n)) ∧
      (CriteriaForFlatness.finiteSequence d).Exact := sorry

/-- Lemma 10.99.5 (2): under the same hypotheses, the cokernel of the rightmost differential
`F 1 → F 0` is flat over `R`. -/
@[stacks 00MI]
theorem flat_cokernel_of_reducedFiniteComplexExact
    {R : Type u} {S : Type v} {n : ℕ} {F : Fin (n + 2) → Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [IsNoetherianRing R] [IsNoetherianRing S]
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    (d : ∀ i : Fin (n + 1), F i.succ →ₗ[S] F i.castSucc)
    (hfinite : ∀ i, Module.Finite S (F i)) (hflat : ∀ i, Module.Flat R (F i))
    (hcomplex : (CriteriaForFlatness.finiteSequence d).IsComplex)
    (hexact_mod :
      Function.Injective
          (((d (Fin.last n)).restrictScalars R).quotientMapByIdeal (maximalIdeal R)) ∧
        (CriteriaForFlatness.reducedFiniteSequence R d).Exact) :
    Module.Flat R (F 0 ⧸ LinearMap.range (d 0)) := sorry

#check @CriteriaForFlatness.finiteSequence
#check @CriteriaForFlatness.reducedFiniteSequence
#check @finiteComplexExact_of_reducedFiniteComplexExact
#check @flat_cokernel_of_reducedFiniteComplexExact

#print axioms CriteriaForFlatness.finiteSequence
#print axioms CriteriaForFlatness.reducedFiniteSequence
#print axioms finiteComplexExact_of_reducedFiniteComplexExact
#print axioms flat_cokernel_of_reducedFiniteComplexExact
