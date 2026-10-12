/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Torsion
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import ReasLib.Algebra.Homology.DerivedCategory.Completeness
public import ReasLib.RingTheory.Kaehler.DeRham
public import stacks_project.Chap60.Example_60_22_2_Presentation

@[expose] public section

noncomputable section

open CategoryTheory
open KaehlerDifferential.DeRham

namespace Crystalline.AffineSpace

/-- Degree-`n` forms of `P` over `ℤ_[p]`, completed `p`-adically. -/
abbrev completedForm (p r n : ℕ) [Fact p.Prime] : Type :=
  AdicCompletion (padicIdeal p) (term ℤ_[p] (polynomialRing p r) n : Type)

/-- `completedForm` is the p-adic completion of algebraic de Rham forms. -/
theorem completedForm_eq (p r n : ℕ) [Fact p.Prime] :
    completedForm p r n =
      AdicCompletion (padicIdeal p) (term ℤ_[p] (polynomialRing p r) n : Type) := sorry

/-- The completed de Rham differential, induced by `KaehlerDifferential.DeRham.d`. -/
def completedDifferential (p r n : ℕ) [Fact p.Prime] :
    completedForm p r n →ₗ[ℤ_[p]] completedForm p r (n + 1) :=
  (AdicCompletion.map (padicIdeal p)
    (d ℤ_[p] (polynomialRing p r) n).hom).restrictScalars ℤ_[p]

/-- On Cauchy representatives, the completed differential applies `DeRham.d` degreewise. -/
theorem completedDifferential_map_mk (p r n : ℕ) [Fact p.Prime]
    (a : AdicCompletion.AdicCauchySequence (padicIdeal p)
      (term ℤ_[p] (polynomialRing p r) n : Type)) :
    completedDifferential p r n (AdicCompletion.mk (padicIdeal p) _ a) =
      AdicCompletion.mk (padicIdeal p) _
        (AdicCompletion.AdicCauchySequence.map (padicIdeal p)
          (d ℤ_[p] (polynomialRing p r) n).hom a) := sorry

/-- Completed degree-`n` forms as a `ℤ_[p]`-module. -/
def completedTerm (p r : ℕ) [Fact p.Prime] (n : ℕ) : ModuleCat.{0} ℤ_[p] :=
  ModuleCat.of ℤ_[p] (completedForm p r n)

/-- `completedTerm` is the module attached to `completedForm`. -/
theorem completedTerm_eq (p r : ℕ) [Fact p.Prime] (n : ℕ) :
    completedTerm p r n = ModuleCat.of ℤ_[p] (completedForm p r n) := sorry

/-- The completed de Rham differential as a morphism of `ℤ_[p]`-modules. -/
def completedDeRhamDifferential (p r : ℕ) [Fact p.Prime] (n : ℕ) :
    completedTerm p r n ⟶ completedTerm p r (n + 1) :=
  ModuleCat.ofHom (completedDifferential p r n)

/-- Consecutive completed differentials compose to zero. -/
theorem completedDeRhamDifferential_sq (p r : ℕ) [Fact p.Prime] (n : ℕ) :
    completedDeRhamDifferential p r n ≫ completedDeRhamDifferential p r (n + 1) = 0 := sorry

/-- The p-adically completed de Rham complex `D → Ω¹ → Ω² → ⋯` of `P` over `ℤ_[p]`. -/
def completedDeRham (p r : ℕ) [Fact p.Prime] :
    CochainComplex (ModuleCat.{0} ℤ_[p]) ℕ :=
  CochainComplex.of (completedTerm p r) (completedDeRhamDifferential p r)
    (completedDeRhamDifferential_sq p r)

/-- Degree `n` of the completed de Rham complex is the completed form module. -/
theorem completedDeRham_X (p r n : ℕ) [Fact p.Prime] :
    (completedDeRham p r).X n = completedTerm p r n := sorry

/-- The differential of the completed de Rham complex is `completedDeRhamDifferential`. -/
theorem completedDeRham_d (p r n : ℕ) [Fact p.Prime] :
    (completedDeRham p r).d n (n + 1) = completedDeRhamDifferential p r n := sorry

/-- Completed forms vanish in degrees above the number of variables. -/
theorem completedTerm_isZero_of_gt (p r i : ℕ) [Fact p.Prime] (hi : r < i) :
    Limits.IsZero (completedTerm p r i) := sorry

/-- The monomial `x^k` as a degree-zero form on the line. -/
def powerZeroForm (p k : ℕ) [Fact p.Prime] : term ℤ_[p] (polynomialRing p 1) 0 :=
  basic ℤ_[p] (polynomialRing p 1) 0 (MvPolynomial.X (0 : Fin 1) ^ k) Fin.elim0

/-- The monomial form `x^k dx` on the line. -/
def monomialOneForm (p k : ℕ) [Fact p.Prime] : term ℤ_[p] (polynomialRing p 1) 1 :=
  basic ℤ_[p] (polynomialRing p 1) 1 (MvPolynomial.X (0 : Fin 1) ^ k)
    (fun _ ↦ MvPolynomial.X (0 : Fin 1))

/-- The completed line differential kills the constant `1`. -/
theorem lineDifferential_one (p : ℕ) [Fact p.Prime] :
    completedDifferential p 1 0
        (AdicCompletion.of (padicIdeal p) _ (powerZeroForm p 0)) = 0 := sorry

/-- On the line, the completed differential acts by `diag(1, 2, 3, …)` on monomials. -/
theorem lineDifferential_monomial (p n : ℕ) [Fact p.Prime] :
    completedDifferential p 1 0
        (AdicCompletion.of (padicIdeal p) _ (powerZeroForm p (n + 1))) =
      (n + 1 : ℤ_[p]) •
        AdicCompletion.of (padicIdeal p) _ (monomialOneForm p n) := sorry

/-- The cokernel of the completed line differential `D → Ω¹_D`. -/
abbrev lineCoker (p : ℕ) [Fact p.Prime] : Type :=
  completedForm p 1 1 ⧸ LinearMap.range (completedDifferential p 1 0)

/-- `lineCoker` is the quotient by the image of the line differential. -/
theorem lineCoker_eq (p : ℕ) [Fact p.Prime] :
    lineCoker p =
      (completedForm p 1 1 ⧸ LinearMap.range (completedDifferential p 1 0)) := sorry

/-- For `r = 1`, degree-one homology is the cokernel of the line differential. -/
theorem lineHomology_equiv_coker (p : ℕ) [Fact p.Prime] :
    IsIsomorphic ((completedDeRham p 1).homology 1) (ModuleCat.of ℤ_[p] (lineCoker p)) := sorry

/-- The summand `ℤ_[p] / nℤ_[p]` for `n > 0`. -/
abbrev torsionComponent (p : ℕ) [Fact p.Prime] (n : {k : ℕ // 0 < k}) : Type :=
  ℤ_[p] ⧸ Submodule.span ℤ_[p] {(n.1 : ℤ_[p])}

/-- `torsionComponent` is the quotient by the principal submodule generated by `n`. -/
theorem torsionComponent_eq (p : ℕ) [Fact p.Prime] (n : {k : ℕ // 0 < k}) :
    torsionComponent p n = (ℤ_[p] ⧸ Submodule.span ℤ_[p] {(n.1 : ℤ_[p])}) := sorry

/-- `⨁_{n > 0} ℤ_[p] / nℤ_[p]`, the torsion subgroup of the line cokernel. -/
abbrev torsionSummand (p : ℕ) [Fact p.Prime] : Type :=
  DirectSum {k : ℕ // 0 < k} (torsionComponent p)

/-- `torsionSummand` is the direct sum of the cyclic modules `ℤ_[p] / n`. -/
theorem torsionSummand_eq (p : ℕ) [Fact p.Prime] :
    torsionSummand p = DirectSum {k : ℕ // 0 < k} (torsionComponent p) := sorry

/-- The class of `x^{n-1} dx` in the line cokernel. -/
def torsionGenerator (p n : ℕ) [Fact p.Prime] : lineCoker p :=
  Submodule.Quotient.mk
    (AdicCompletion.of (padicIdeal p) (term ℤ_[p] (polynomialRing p 1) 1 : Type)
      (monomialOneForm p (n - 1)))

/-- `torsionGenerator` is the class of the completed monomial `x^{n-1} dx`. -/
theorem torsionGenerator_eq (p n : ℕ) [Fact p.Prime] :
    torsionGenerator p n =
      Submodule.Quotient.mk
        (AdicCompletion.of (padicIdeal p) (term ℤ_[p] (polynomialRing p 1) 1 : Type)
          (monomialOneForm p (n - 1))) := sorry

/-- The class of `x^{n-1} dx` is killed by `n`. -/
theorem torsionGenerator_n_smul (p n : ℕ) [Fact p.Prime] (hn : 0 < n) :
    n • torsionGenerator p n = 0 := sorry

/-- The classes of `x^{n-1} dx` assemble to an injection of `⨁_{n > 0} ℤ_[p] / n`. -/
theorem exists_injective_torsionSummand (p : ℕ) [Fact p.Prime] :
    ∃ f : torsionSummand p →ₗ[ℤ_[p]] lineCoker p, Function.Injective f := sorry

/-- Coefficient of `x^n dx` in `ω = ∑_{e > 0} p^e x^{p^{2e}-1} dx`. -/
def omegaCoeff (p : ℕ) [Fact p.Prime] (n : ℕ) : ℤ_[p] :=
  Finset.sum (Finset.range (n + 2)) fun e ↦
    if n + 1 = p ^ (2 * e) ∧ 0 < e then (p : ℤ_[p]) ^ e else 0

/-- On the source support of `ω`, the coefficient of `x^{p^{2e}-1} dx` is `p^e`. -/
theorem omegaCoeff_apply (p e : ℕ) [Fact p.Prime] (he : 0 < e) :
    omegaCoeff p (p ^ (2 * e) - 1) = (p : ℤ_[p]) ^ e := sorry

/-- Partial sums of `ω = ∑_{e > 0} p^e x^{p^{2e}-1} dx`. -/
def omegaPartial (p : ℕ) [Fact p.Prime] (N : ℕ) : term ℤ_[p] (polynomialRing p 1) 1 :=
  Finset.sum (Finset.range N) fun e ↦
    (p : ℤ_[p]) ^ (e + 1) • monomialOneForm p (p ^ (2 * (e + 1)) - 1)

/-- Successive partial sums of `ω` are congruent modulo `p^N`. -/
theorem omegaPartial_succ (p : ℕ) [Fact p.Prime] (N : ℕ) :
    omegaPartial p N ≡ omegaPartial p (N + 1)
      [SMOD (padicIdeal p ^ N • ⊤ :
        Submodule ℤ_[p] (term ℤ_[p] (polynomialRing p 1) 1 : Type))] := sorry

/-- No nonzero integer kills all finite partial sums of `ω` in the line cokernel. -/
theorem omega_not_isOfFinAddOrder (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : 0 < m) :
    ∃ N : ℕ,
      m • (Submodule.Quotient.mk
        (AdicCompletion.of (padicIdeal p) _
          (omegaPartial p N)) : lineCoker p) ≠ 0 := sorry

/-- Coefficient of `x^n dx` in `η = ∑_{e > 0} p^e x^{p^e-1} dx`. -/
def etaCoeff (p : ℕ) [Fact p.Prime] (n : ℕ) : ℤ_[p] :=
  Finset.sum (Finset.range (n + 2)) fun e ↦
    if n + 1 = p ^ e ∧ 0 < e then (p : ℤ_[p]) ^ e else 0

/-- On the source support of `η`, the coefficient of `x^{p^e-1} dx` is `p^e`. -/
theorem etaCoeff_apply (p e : ℕ) [Fact p.Prime] (he : 0 < e) :
    etaCoeff p (p ^ e - 1) = (p : ℤ_[p]) ^ e := sorry

/-- Partial sums of `η = ∑_{e > 0} p^e x^{p^e-1} dx`. -/
def etaPartial (p : ℕ) [Fact p.Prime] (N : ℕ) : term ℤ_[p] (polynomialRing p 1) 1 :=
  Finset.sum (Finset.range N) fun e ↦
    (p : ℤ_[p]) ^ (e + 1) • monomialOneForm p (p ^ (e + 1) - 1)

/-- Successive partial sums of `η` are congruent modulo `p^N`. -/
theorem etaPartial_succ (p : ℕ) [Fact p.Prime] (N : ℕ) :
    etaPartial p N ≡ etaPartial p (N + 1)
      [SMOD (padicIdeal p ^ N • ⊤ :
        Submodule ℤ_[p] (term ℤ_[p] (polynomialRing p 1) 1 : Type))] := sorry

/-- Finite `p^t`-root tail `∑_{e = t+1}^{N} p^{e-t} x^{p^e-1} dx` of `η`. -/
def etaRootPartial (p : ℕ) [Fact p.Prime] (t N : ℕ) :
    term ℤ_[p] (polynomialRing p 1) 1 :=
  Finset.sum (Finset.range (N + 1)) fun e ↦
    if t + 1 ≤ e then (p : ℤ_[p]) ^ (e - t) • monomialOneForm p (p ^ e - 1) else 0

/-- `etaRootPartial` retains the terms of `η` of index `> t`, scaled by `p^{-t}`. -/
theorem etaRootPartial_eq (p t N : ℕ) [Fact p.Prime] :
    etaRootPartial p t N =
      Finset.sum (Finset.range (N + 1)) fun e ↦
        if t + 1 ≤ e then (p : ℤ_[p]) ^ (e - t) • monomialOneForm p (p ^ e - 1)
        else 0 := sorry

/-- The head of `η` is exact, so the class of a partial sum is `p^t` times the tail. -/
theorem eta_class_mem_smul (p t N : ℕ) [Fact p.Prime] (ht : 0 < t) (hN : t ≤ N) :
    AdicCompletion.of (padicIdeal p) _ (etaPartial p N) -
        (p : ℤ_[p]) ^ t • AdicCompletion.of (padicIdeal p) _ (etaRootPartial p t N) ∈
      LinearMap.range (completedDifferential p 1 0) := sorry

/-- The Cauchy sequence of partial sums of `η` is not in the image of the completed
line differential. -/
theorem eta_not_mem_range (p : ℕ) [Fact p.Prime] :
    ¬ ∃ x : completedForm p 1 0, ∀ N : ℕ,
        completedDifferential p 1 0 x ≡
          AdicCompletion.of (padicIdeal p) _ (etaPartial p N)
        [SMOD (padicIdeal p ^ N • ⊤ : Submodule ℤ_[p] (completedForm p 1 1))] := sorry

/-- Partial sums of the would-be primitive `a + ∑_{e > 0} x^{p^e}`. -/
def etaPrimitivePartial (p : ℕ) [Fact p.Prime] (a : ℤ_[p]) (N : ℕ) : polynomialRing p 1 :=
  MvPolynomial.C a +
    Finset.sum (Finset.range N) fun e ↦ MvPolynomial.X (0 : Fin 1) ^ (p ^ (e + 1))

/-- `a + ∑_{e > 0} x^{p^e}` is not a p-adic Cauchy sequence in `P`. -/
theorem etaPrimitive_not_adicCauchy (p : ℕ) [Fact p.Prime] (a : ℤ_[p]) :
    ¬ AdicCompletion.IsAdicCauchy (padicIdeal p) (polynomialRing p 1)
        (fun N ↦ etaPrimitivePartial p a N) := sorry

/-- Homology of the completed de Rham complex is a derived-complete `ℤ_[p]`-module. -/
theorem homology_derivedComplete (p r i : ℕ) [Fact p.Prime] :
    ModuleCat.IsDerivedCompleteWithRespectTo ((completedDeRham p r).homology i)
      (padicIdeal p) := sorry

end Crystalline.AffineSpace
