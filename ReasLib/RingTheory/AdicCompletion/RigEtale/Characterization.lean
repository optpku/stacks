/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.AdicCompletion.RigEtale
public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent.Derived
public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent.InverseSystem
public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent.Fitting

/-!
# Characterization of rig-étale algebras

For a topologically finite type algebra over a Noetherian pair, rig-étaleness
is equivalent to annihilation of the completed naive cotangent object or its
homology, uniform annihilation at positive adic stages, full-size relation
and Jacobian conditions, and power containment in the Jacobian and Cramer ideals.
-/

open CategoryTheory

@[expose] public section

noncomputable section

universe u

namespace Algebra.NaiveCotangent.Adic
namespace Presentation

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {I : Ideal A} {ι : Type u}

/-- Multiplication by every element of `I ^ c` is zero on
`naiveCotangentObject I P` in `D(B)`. -/
def powSmulIdEqZero [Fintype ι] (P : Presentation A B I ι) (c : ℕ) : Prop :=
  ∀ a ∈ I ^ c, (algebraMap A B a) • 𝟙 (naiveCotangentObject I P) = 0

/-- Vanishing of `I ^ c` on the derived completed naive cotangent object unpacks
as scalar annihilation of the identity morphism. -/
theorem powSmulIdEqZero_iff [Fintype ι] (P : Presentation A B I ι) (c : ℕ) :
    P.powSmulIdEqZero c ↔
      ∀ a ∈ I ^ c, (algebraMap A B a) • 𝟙 (naiveCotangentObject I P) = 0 :=
  sorry

/-- The extended power `I ^ c` annihilates homology of `naiveCotangent I P` in
homological degrees `1` and `0`. -/
def homologyAnnihilated [Fintype ι] (P : Presentation A B I ι) (c : ℕ) : Prop :=
  (I ^ c).map (algebraMap A B) ≤
      Module.annihilator B ((naiveCotangent I P).homology 1 : Type u) ∧
    (I ^ c).map (algebraMap A B) ≤
      Module.annihilator B ((naiveCotangent I P).homology 0 : Type u)

/-- Annihilation of completed naive cotangent homology unpacks as containment in
both degree `1` and degree `0` annihilators. -/
theorem homologyAnnihilated_iff [Fintype ι] (P : Presentation A B I ι) (c : ℕ) :
    P.homologyAnnihilated c ↔
      (I ^ c).map (algebraMap A B) ≤
          Module.annihilator B ((naiveCotangent I P).homology 1 : Type u) ∧
        (I ^ c).map (algebraMap A B) ≤
          Module.annihilator B ((naiveCotangent I P).homology 0 : Type u) :=
  sorry

/-- Annihilation of chain-complex homology in degrees `1` and `0` is equivalent
to annihilation of derived homology in degrees `-1` and `0`. -/
theorem homologyAnnihilated_iff_derived [Fintype ι] (P : Presentation A B I ι)
    (c : ℕ) :
    P.homologyAnnihilated c ↔
      (I ^ c).map (algebraMap A B) ≤
          Module.annihilator B
            ((DerivedCategory.homologyFunctor (ModuleCat B) (-1)).obj
              (naiveCotangentObject I P)) ∧
        (I ^ c).map (algebraMap A B) ≤
          Module.annihilator B
            ((DerivedCategory.homologyFunctor (ModuleCat B) 0).obj
              (naiveCotangentObject I P)) :=
  sorry

/-- The extended power `I ^ c` annihilates homology in degrees `1` and `0`
at every positive adic stage, with stage `n` taken modulo `I ^ (n + 1)`. -/
def stageHomologyAnnihilated [Fintype ι] (P : Presentation A B I ι) (c : ℕ) :
    Prop :=
  ∀ n : ℕ,
    (I ^ c).map (algebraMap A (B ⧸ stageIdeal I n)) ≤
        Module.annihilator (B ⧸ stageIdeal I n)
          ((stageComplex I P n).homology 1 : Type u) ∧
      (I ^ c).map (algebraMap A (B ⧸ stageIdeal I n)) ≤
        Module.annihilator (B ⧸ stageIdeal I n)
          ((stageComplex I P n).homology 0 : Type u)

/-- Stagewise homology annihilation unpacks as containment in both degree `1`
and degree `0` annihilators of every `stageComplex I P n`. -/
theorem stageHomologyAnnihilated_iff [Fintype ι] (P : Presentation A B I ι)
    (c : ℕ) :
    P.stageHomologyAnnihilated c ↔
      ∀ n : ℕ,
        (I ^ c).map (algebraMap A (B ⧸ stageIdeal I n)) ≤
            Module.annihilator (B ⧸ stageIdeal I n)
              ((stageComplex I P n).homology 1 : Type u) ∧
          (I ^ c).map (algebraMap A (B ⧸ stageIdeal I n)) ≤
            Module.annihilator (B ⧸ stageIdeal I n)
              ((stageComplex I P n).homology 0 : Type u) :=
  sorry

/-- For every `a ∈ I`, some power `a ^ c` annihilates
`H_0(naiveCotangent I P)` and `r = Fintype.card ι` kernel elements satisfy the
completed relation condition. -/
def existsRelationGenerators [Fintype ι] (P : Presentation A B I ι) : Prop :=
  ∀ a ∈ I, ∃ c : ℕ,
    algebraMap A B (a ^ c) ∈
        Module.annihilator B ((naiveCotangent I P).homology 0 : Type u) ∧
      ∃ fs : Fin (Fintype.card ι) → P.ker,
        relationCondition P (algebraMap A B (a ^ c)) fs

/-- Existence of relation generators is equivalent to degree-zero homology
annihilation and the relation condition for a full-size tuple of kernel elements. -/
theorem existsRelationGenerators_iff [Fintype ι] (P : Presentation A B I ι) :
    P.existsRelationGenerators ↔
      ∀ a ∈ I, ∃ c : ℕ,
        algebraMap A B (a ^ c) ∈
            Module.annihilator B ((naiveCotangent I P).homology 0 : Type u) ∧
          ∃ fs : Fin (Fintype.card ι) → P.ker,
            relationCondition P (algebraMap A B (a ^ c)) fs :=
  sorry

/-- For every `a ∈ I`, some power `a ^ c` is elementary for a square completed
Jacobian minor on `r = Fintype.card ι` relations and columns. -/
def existsElementarySquare [Fintype ι] (P : Presentation A B I ι) : Prop :=
  ∀ a ∈ I, ∃ (c : ℕ) (fs : Fin (Fintype.card ι) → P.ker)
      (cols : Fin (Fintype.card ι) ↪ ι),
    IsElementaryFor P (algebraMap A B (a ^ c)) fs cols

/-- Existence of elementary squares is equivalent to elementary full-size
Jacobian data for a power of every element of `I`. -/
theorem existsElementarySquare_iff [Fintype ι] (P : Presentation A B I ι) :
    P.existsElementarySquare ↔
      ∀ a ∈ I, ∃ (c : ℕ) (fs : Fin (Fintype.card ι) → P.ker)
          (cols : Fin (Fintype.card ι) ↪ ι),
        IsElementaryFor P (algebraMap A B (a ^ c)) fs cols :=
  sorry

/-- Some extended power `I ^ c` is contained in both the Jacobian ideal and the
Cramer ideal. -/
def fittingContainsPow [Fintype ι] (P : Presentation A B I ι) : Prop :=
  ∃ c : ℕ,
    (I ^ c).map (algebraMap A B) ≤ P.jacobianIdeal ∧
      (I ^ c).map (algebraMap A B) ≤ P.cramerIdeal

/-- Fitting containment unpacks as a single exponent whose extended power lies
in both completed Fitting ideals. -/
theorem fittingContainsPow_iff [Fintype ι] (P : Presentation A B I ι) :
    P.fittingContainsPow ↔
      ∃ c : ℕ,
        (I ^ c).map (algebraMap A B) ≤ P.jacobianIdeal ∧
          (I ^ c).map (algebraMap A B) ≤ P.cramerIdeal :=
  sorry

end Presentation
end Algebra.NaiveCotangent.Adic

open Algebra.NaiveCotangent.Adic

/-- For a Noetherian ring `A`, an ideal `I`, and an algebra `B`
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
