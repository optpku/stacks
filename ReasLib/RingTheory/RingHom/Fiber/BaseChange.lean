/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.LocalRing.ResidueField.Map

@[expose] public section

/-!
# Base change of residue-field fibers

@stack 0BRB
@stack 00FI

This leaf owns the canonical algebra equivalence between a residue-field fiber
after tensor-product base change and the corresponding scalar extension of the
original fiber.
-/

noncomputable section

open scoped TensorProduct

universe u v w

namespace Ideal.Fiber

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- The residue-field fiber of `R' ⊗[R] S` over `p' : Spec R'` is canonically the scalar
extension of the fiber of `S` over the contraction of `p'` to `R`. -/
@[stacks 0BRB "fiber of tensor-product base change"]
noncomputable def baseChangeAlgEquiv
    {R' : Type w} [CommRing R'] [Algebra R R']
    (p' : PrimeSpectrum R') :
    let p := p'.asIdeal.under R
    -- Local instance justification (proof-local temporary data): contraction makes `p'` lie over `p`.
    letI : p'.asIdeal.LiesOver p := ⟨rfl⟩
    -- Local instance justification (instance diamond): fix the induced residue-field algebra without creating a competing global path.
    letI : Algebra p.ResidueField p'.asIdeal.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver p p'.asIdeal
    p'.asIdeal.Fiber (R' ⊗[R] S) ≃ₐ[p'.asIdeal.ResidueField]
      p'.asIdeal.ResidueField ⊗[p.ResidueField] p.Fiber S :=
  let p := p'.asIdeal.under R
  -- Local instance justification (proof-local temporary data): contraction makes `p'` lie over `p`.
  letI : p'.asIdeal.LiesOver p := ⟨rfl⟩
  -- Local instance justification (instance diamond): fix the canonical residue-field algebra without creating a competing global path.
  letI : Algebra p.ResidueField p'.asIdeal.ResidueField :=
    Ideal.ResidueField.algebraOfLiesOver p p'.asIdeal
  -- Local instance justification (defeq pin): fix the scalar tower for the selected residue-field algebra.
  letI : IsScalarTower R p.ResidueField p'.asIdeal.ResidueField :=
    Ideal.ResidueField.isScalarTower_of_liesOver p p'.asIdeal
  (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).trans
    (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm

/-- If the residue-field map at a base-change point is bijective, its fiber after
base change is canonically ring-equivalent to the original fiber. -/
@[stacks 0BRB "fiber base change with bijective residue fields"]
noncomputable def baseChangeRingEquiv
    {R' : Type w} [CommRing R'] [Algebra R R']
    (p : Ideal R) [p.IsPrime] (q : Ideal R') [q.IsPrime] [q.LiesOver p]
    (hκ : Function.Bijective
      (Ideal.ResidueField.map p q (algebraMap R R') (q.over_def p))) :
    q.Fiber (R' ⊗[R] S) ≃+* p.Fiber S :=
  -- Local declaration justification (instance diamond): Mathlib deliberately keeps the
  -- localized lying-over algebra explicit because registering it globally creates competing paths.
  let _ : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  let e : q.Fiber (R' ⊗[R] S) ≃ₐ[p.ResidueField] p.Fiber S :=
    ((Algebra.TensorProduct.cancelBaseChange
      R R' q.ResidueField q.ResidueField S).restrictScalars _).trans
      (Algebra.TensorProduct.congr
        (.symm <| .ofBijective (Algebra.ofId _ _) hκ)
        (AlgEquiv.refl : S ≃ₐ[R] S))
  e.toRingEquiv

/-- Under `baseChangeAlgEquiv`, the canonical image of `s : S` in the scalar-extension model
is the nested pure tensor `1 ⊗ₜ (1 ⊗ₜ s)`. -/
@[stacks 0BRB "base-change fiber equivalence on a canonical tensor"]
theorem baseChangeAlgEquiv_symm_includeRight_tmul
    {R' : Type w} [CommRing R'] [Algebra R R']
    (p' : PrimeSpectrum R') (s : S) :
    let p := p'.asIdeal.under R
    -- Local instance justification (proof-local temporary data): contraction makes `p'` lie over `p`.
    letI : p'.asIdeal.LiesOver p := ⟨rfl⟩
    -- Local instance justification (instance diamond): fix the induced residue-field algebra without creating a competing global path.
    letI : Algebra p.ResidueField p'.asIdeal.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver p p'.asIdeal
    (baseChangeAlgEquiv (R := R) (S := S) p').symm
        ((1 : p'.asIdeal.ResidueField) ⊗ₜ ((1 : p.ResidueField) ⊗ₜ[R] s)) =
      (1 : p'.asIdeal.ResidueField) ⊗ₜ[R'] ((1 : R') ⊗ₜ[R] s) := sorry

/-- A nontrivial residue-field fiber remains nontrivial after arbitrary tensor-product base
change. -/
@[stacks 00FI]
theorem nontrivial_baseChange
    {R' : Type w} [CommRing R'] [Algebra R R']
    (p' : PrimeSpectrum R')
    (h : Nontrivial ((p'.asIdeal.under R).Fiber S)) :
    Nontrivial (p'.asIdeal.Fiber (R' ⊗[R] S)) := sorry

end Ideal.Fiber
