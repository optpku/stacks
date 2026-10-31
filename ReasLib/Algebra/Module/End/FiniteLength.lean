/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import ReasLib.Algebra.Module.CompositionSeries.Factor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Endomorphisms of finite-length modules

This file owns the determinant, trace, and characteristic polynomial of an endomorphism of a
finite-length module over a local ring.  The concrete values are computed on the simple factors of
an endomorphism-stable composition series; the Jordan--Hölder uniqueness theorems make the values
independent of the chosen stable series.
-/

@[expose] public section

noncomputable section

open CategoryTheory IsLocalRing ModuleCat Polynomial
open Module.CompositionSeries
open scoped BigOperators TensorProduct

universe u v

namespace Module.End

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The polynomial-module structure in which `X` acts through an endomorphism `φ`. -/
@[stacks 0GSY "polynomial-module structure of an endomorphism"]
abbrev toPolynomialModule (φ : Module.End R M) : Module R[X] M :=
  Module.compHom M (aeval φ).toRingHom

/-- A composition series by `φ`-stable submodules, represented as `R[X]`-submodules. -/
@[stacks 0GSY "endomorphism-stable composition series"]
abbrev StableCompositionSeries (φ : Module.End R M) :=
  let _ : Module R[X] M := φ.toPolynomialModule
  {s : CompositionSeries (Submodule R[X] M) // s.head = ⊥ ∧ s.last = ⊤}

namespace StableCompositionSeries

variable {φ : Module.End R M}

/-- Restricting the polynomial action along `R → R[X]` gives the scalar tower used by the factor
endomorphism. -/
@[stacks 0GSY "scalar tower on a stable composition factor"]
noncomputable instance factorIsScalarTower
    (s : StableCompositionSeries φ) (i : Fin s.1.length) :
    let _ : Module R[X] M := φ.toPolynomialModule
    let _ : Module R (factor s.1 i) :=
      Module.compHom (factor s.1 i) (C : R →+* R[X])
    IsScalarTower R R[X] (factor s.1 i) := by
  letI : Module R[X] M := φ.toPolynomialModule
  letI : Module R (factor s.1 i) :=
    Module.compHom (factor s.1 i) (C : R →+* R[X])
  refine ⟨?_⟩
  intro r p x
  rw [Algebra.smul_def]
  exact mul_smul (C r) p x
-- Proof strategy: unfold both `Module.compHom` actions and apply the scalar-tower constructor;
-- evaluation of `C r` on the factor agrees definitionally with the restricted `R`-action.

/-- The `R`-linear endomorphism induced by the action of `X` on a composition factor. -/
@[stacks 0GSY "endomorphism induced on a stable composition factor"]
noncomputable def factorMap (s : StableCompositionSeries φ) (i : Fin s.1.length) :
    let _ : Module R[X] M := φ.toPolynomialModule
    let _ : Module R (factor s.1 i) :=
      Module.compHom (factor s.1 i) (C : R →+* R[X])
    factor s.1 i →ₗ[R] factor s.1 i :=
  -- Local instance justification (defeq pin): the factor inherits the chosen polynomial action.
  letI : Module R[X] M := φ.toPolynomialModule
  -- Local instance justification (defeq pin): restrict that action along the coefficient map.
  letI : Module R (factor s.1 i) :=
    Module.compHom (factor s.1 i) (C : R →+* R[X])
  ((LinearMap.lsmul R[X] (factor s.1 i)) X).restrictScalars R

section LocalRing

variable [IsLocalRing R]

/-- A simple composition factor becomes finite-dimensional after base change to the residue
field. -/
@[stacks 0GSY "finite-dimensional residue-field composition factor"]
noncomputable instance factorFiniteDimensional
    (s : StableCompositionSeries φ) (i : Fin s.1.length) :
    let _ : Module R[X] M := φ.toPolynomialModule
    let _ : Module R (factor s.1 i) :=
      Module.compHom (factor s.1 i) (C : R →+* R[X])
    FiniteDimensional (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] factor s.1 i) := sorry
-- Proof strategy: use simplicity of `CompositionSeries.factor` to identify the underlying
-- nonzero `R`-module factor with a residue-field vector space of finite dimension, then transport
-- finite-dimensionality through the canonical tensor/base-change equivalence.

/-- The residue-field endomorphism induced on a simple composition factor. -/
@[stacks 0GSY "residue-field endomorphism on a stable factor"]
noncomputable abbrev factorResidueFieldMap
    (s : StableCompositionSeries φ) (i : Fin s.1.length) :
    let _ : Module R[X] M := φ.toPolynomialModule
    let _ : Module R (factor s.1 i) :=
      Module.compHom (factor s.1 i) (C : R →+* R[X])
    IsLocalRing.ResidueField R ⊗[R] factor s.1 i →ₗ[IsLocalRing.ResidueField R]
      IsLocalRing.ResidueField R ⊗[R] factor s.1 i :=
  -- Local instance justification (defeq pin): the factor inherits the chosen polynomial action.
  letI : Module R[X] M := φ.toPolynomialModule
  -- Local instance justification (defeq pin): use the coefficient-restricted factor module.
  letI : Module R (factor s.1 i) :=
    Module.compHom (factor s.1 i) (C : R →+* R[X])
  (factorMap s i).baseChange (IsLocalRing.ResidueField R)

/-- The determinant contributed by one simple composition factor. -/
@[stacks 0GSY "determinant of a stable composition factor"]
noncomputable def factorDet (s : StableCompositionSeries φ) (i : Fin s.1.length) :
    IsLocalRing.ResidueField R :=
  -- Local instance justification (defeq pin): the factor inherits the chosen polynomial action.
  letI : Module R[X] M := φ.toPolynomialModule
  -- Local instance justification (defeq pin): use the coefficient-restricted factor module.
  letI : Module R (factor s.1 i) :=
    Module.compHom (factor s.1 i) (C : R →+* R[X])
  (factorResidueFieldMap s i).det

/-- The trace contributed by one simple composition factor. -/
@[stacks 0GSY "trace of a stable composition factor"]
noncomputable def factorTrace (s : StableCompositionSeries φ) (i : Fin s.1.length) :
    IsLocalRing.ResidueField R :=
  -- Local instance justification (defeq pin): the factor inherits the chosen polynomial action.
  letI : Module R[X] M := φ.toPolynomialModule
  -- Local instance justification (defeq pin): use the coefficient-restricted factor module.
  letI : Module R (factor s.1 i) :=
    Module.compHom (factor s.1 i) (C : R →+* R[X])
  LinearMap.trace (IsLocalRing.ResidueField R)
    (IsLocalRing.ResidueField R ⊗[R] factor s.1 i) (factorResidueFieldMap s i)

/-- The characteristic polynomial contributed by one simple composition factor. -/
@[stacks 0GSY "characteristic polynomial of a stable composition factor"]
noncomputable def factorCharpoly
    (s : StableCompositionSeries φ) (i : Fin s.1.length) :
    Polynomial (IsLocalRing.ResidueField R) :=
  -- Local instance justification (defeq pin): the factor inherits the chosen polynomial action.
  letI : Module R[X] M := φ.toPolynomialModule
  -- Local instance justification (defeq pin): use the coefficient-restricted factor module.
  letI : Module R (factor s.1 i) :=
    Module.compHom (factor s.1 i) (C : R →+* R[X])
  (factorResidueFieldMap s i).charpoly

/-- The determinant computed from a chosen stable composition series. -/
@[stacks 0GSY "determinant computed from a stable composition series"]
noncomputable def det (s : StableCompositionSeries φ) : IsLocalRing.ResidueField R :=
  ∏ i : Fin s.1.length, factorDet s i

/-- The trace computed from a chosen stable composition series. -/
@[stacks 0GSY "trace computed from a stable composition series"]
noncomputable def trace (s : StableCompositionSeries φ) : IsLocalRing.ResidueField R :=
  ∑ i : Fin s.1.length, factorTrace s i

/-- The characteristic polynomial computed from a chosen stable composition series. -/
@[stacks 0GSY "characteristic polynomial from a stable composition series"]
noncomputable def charpoly (s : StableCompositionSeries φ) :
    Polynomial (IsLocalRing.ResidueField R) :=
  ∏ i : Fin s.1.length, factorCharpoly s i

private theorem factor_invariants_eq_of_linearEquiv (s t : StableCompositionSeries φ) (i : Fin s.1.length) (j : Fin t.1.length)
    (h : letI : Module R[X] M := φ.toPolynomialModule
      Nonempty (factor s.1 i ≃ₗ[R[X]] factor t.1 j)) :
    s.factorDet i = t.factorDet j ∧ s.factorTrace i = t.factorTrace j ∧
      s.factorCharpoly i = t.factorCharpoly j := by
  letI : Module R[X] M := φ.toPolynomialModule
  letI : Module R (factor s.1 i) := Module.compHom (factor s.1 i) (C : R →+* R[X])
  letI : Module R (factor t.1 j) := Module.compHom (factor t.1 j) (C : R →+* R[X])
  obtain ⟨e⟩ := h
  let er := e.restrictScalars R
  let ek := LinearEquiv.baseChange R (ResidueField R) _ _ er
  have he : ek.conj (s.factorResidueFieldMap i) = t.factorResidueFieldMap j := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      simp only [LinearEquiv.conj_apply_apply, LinearMap.baseChange_tmul,
        StableCompositionSeries.factorResidueFieldMap,
        StableCompositionSeries.factorMap]
      change TensorProduct.tmul R a (e ((X : R[X]) • e.symm x)) = TensorProduct.tmul R a ((X : R[X]) • x)
      rw [e.map_smul, e.apply_symm_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  refine ⟨?_, ?_, ?_⟩
  · change (s.factorResidueFieldMap i).det = (t.factorResidueFieldMap j).det
    rw [← he]
    exact (LinearMap.det_conj _ ek).symm
  · change LinearMap.trace _ _ (s.factorResidueFieldMap i) =
      LinearMap.trace _ _ (t.factorResidueFieldMap j)
    rw [← he]
    exact (LinearMap.trace_conj' _ ek).symm
  · change (s.factorResidueFieldMap i).charpoly = (t.factorResidueFieldMap j).charpoly
    rw [← he]
    exact (LinearEquiv.charpoly_conj ek _).symm

private theorem invariants_eq (s t : StableCompositionSeries φ) :
    s.det = t.det ∧ s.trace = t.trace ∧ s.charpoly = t.charpoly := by
  letI : Module R[X] M := φ.toPolynomialModule
  obtain ⟨σ, hσ⟩ :=
    s.1.jordan_holder t.1 (s.2.1.trans t.2.1.symm) (s.2.2.trans t.2.2.symm)
  have h i := factor_invariants_eq_of_linearEquiv s t i (σ i) (hσ i)
  refine ⟨?_, ?_, ?_⟩
  · show (∏ i, s.factorDet i) = ∏ i, t.factorDet i
    calc
      (∏ i, s.factorDet i) = ∏ i, t.factorDet (σ i) :=
        Finset.prod_congr rfl fun i _ => (h i).1
      _ = ∏ i, t.factorDet i := σ.prod_comp _
  · show (∑ i, s.factorTrace i) = ∑ i, t.factorTrace i
    calc
      (∑ i, s.factorTrace i) = ∑ i, t.factorTrace (σ i) :=
        Finset.sum_congr rfl fun i _ => (h i).2.1
      _ = ∑ i, t.factorTrace i := σ.sum_comp _
  · show (∏ i, s.factorCharpoly i) = ∏ i, t.factorCharpoly i
    calc
      (∏ i, s.factorCharpoly i) = ∏ i, t.factorCharpoly (σ i) :=
        Finset.prod_congr rfl fun i _ => (h i).2.2
      _ = ∏ i, t.factorCharpoly i := σ.prod_comp _

end LocalRing

end StableCompositionSeries

section LocalRing

variable [IsLocalRing R]

private theorem nonempty_stableCompositionSeries [IsNoetherian R M] [IsArtinian R M]
    (φ : Module.End R M) : Nonempty (StableCompositionSeries φ) := by
  letI : Module R[X] M := φ.toPolynomialModule
  letI : IsScalarTower R R[X] M :=
    IsScalarTower.of_algebraMap_smul fun r x => by
      change (aeval φ) (C r) x = r • x
      simp
  letI : IsNoetherian R[X] M := isNoetherian_of_tower R inferInstance
  letI : IsArtinian R[X] M := isArtinian_of_tower R inferInstance
  obtain ⟨s, hs⟩ := exists_compositionSeries_of_isNoetherian_isArtinian R[X] M
  exact ⟨⟨s, hs⟩⟩

/-- The stable-series determinant has a unique value when the underlying module is noetherian
and artinian. -/
@[stacks 0GSY "Jordan-Hoelder invariance of the stable determinant"]
theorem existsUnique_stableDet [IsNoetherian R M] [IsArtinian R M]
    (φ : Module.End R M) :
    ∃! a : IsLocalRing.ResidueField R, ∀ s : StableCompositionSeries φ, a = s.det := by
  obtain ⟨s⟩ := nonempty_stableCompositionSeries φ
  refine ⟨s.det, ?_, ?_⟩
  · intro t
    exact (StableCompositionSeries.invariants_eq s t).1
  · intro a ha
    exact ha s
-- Proof strategy: obtain stable composition series from finite length over `R[X]`; compare any two
-- by Jordan--Hölder, transport the conjugate residue-field factor maps along the factor
-- equivalences, and use determinant invariance plus permutation invariance of the finite product.

/-- The stable-series trace has a unique value when the underlying module is noetherian and
artinian. -/
@[stacks 0GSY "Jordan-Hoelder invariance of the stable trace"]
theorem existsUnique_stableTrace [IsNoetherian R M] [IsArtinian R M]
    (φ : Module.End R M) :
    ∃! a : IsLocalRing.ResidueField R, ∀ s : StableCompositionSeries φ, a = s.trace := by
  obtain ⟨s⟩ := nonempty_stableCompositionSeries φ
  refine ⟨s.trace, ?_, ?_⟩
  · intro t
    exact (StableCompositionSeries.invariants_eq s t).2.1
  · intro a ha
    exact ha s
-- Proof strategy: use the same Jordan--Hölder matching of stable factors as for determinant;
-- trace is invariant under conjugacy and the matched factor traces have the same finite sum.

/-- The stable-series characteristic polynomial has a unique value when the underlying module is
noetherian and artinian. -/
@[stacks 0GSY "Jordan-Hoelder invariance of the stable characteristic polynomial"]
theorem existsUnique_stableCharpoly [IsNoetherian R M] [IsArtinian R M]
    (φ : Module.End R M) :
    ∃! p : Polynomial (IsLocalRing.ResidueField R),
      ∀ s : StableCompositionSeries φ, p = s.charpoly := by
  obtain ⟨s⟩ := nonempty_stableCompositionSeries φ
  refine ⟨s.charpoly, ?_, ?_⟩
  · intro t
    exact (StableCompositionSeries.invariants_eq s t).2.2
  · intro a ha
    exact ha s
-- Proof strategy: match the stable composition factors by Jordan--Hölder, use characteristic-
-- polynomial invariance under the induced conjugacies, and compare the products after reindexing.

/-- A fixed endomorphism-stable composition series of a finite-length module. -/
private noncomputable def someStableCompositionSeries
    (φ : Module.End R M) (hM : IsFiniteLength R M) : StableCompositionSeries φ :=
  -- Local instance justification (defeq pin): use the polynomial action determined by `φ`.
  letI : Module R[X] M := φ.toPolynomialModule
  -- Local instance justification (proof-local temporary data): the polynomial action restricts to the original `R`-module structure.
  letI : IsScalarTower R R[X] M :=
    IsScalarTower.of_algebraMap_smul fun r x => by
      change (aeval φ) (C r) x = r • x
      simp
  -- Local instance justification (proof-local temporary data): stable submodules inherit the ascending-chain condition from the finite-length `R`-module.
  letI : IsNoetherian R[X] M :=
    isNoetherian_of_tower R (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).1
  -- Local instance justification (proof-local temporary data): stable submodules inherit the descending-chain condition from the finite-length `R`-module.
  letI : IsArtinian R[X] M :=
    isArtinian_of_tower R (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).2
  let h := exists_compositionSeries_of_isNoetherian_isArtinian R[X] M
  ⟨h.choose, h.choose_spec⟩

/-- The determinant of an endomorphism of a finite-length module over a local ring. -/
@[no_expose, stacks 0GSY "determinant of a finite-length endomorphism"]
noncomputable def finiteLengthDeterminant
    (φ : Module.End R M) (hM : IsFiniteLength R M) : IsLocalRing.ResidueField R :=
  (someStableCompositionSeries φ hM).det

/-- The trace of an endomorphism of a finite-length module over a local ring. -/
@[no_expose, stacks 0GSY "trace of a finite-length endomorphism"]
noncomputable def finiteLengthTrace
    (φ : Module.End R M) (hM : IsFiniteLength R M) : IsLocalRing.ResidueField R :=
  (someStableCompositionSeries φ hM).trace

/-- The characteristic polynomial of an endomorphism of a finite-length module over a local
ring. -/
@[no_expose, stacks 0GSY "characteristic polynomial of a finite-length endomorphism"]
noncomputable def finiteLengthCharpoly
    (φ : Module.End R M) (hM : IsFiniteLength R M) :
    Polynomial (IsLocalRing.ResidueField R) :=
  (someStableCompositionSeries φ hM).charpoly

/-- Any stable composition series computes the canonical finite-length determinant. -/
@[stacks 0GSY "stable-series formula for the finite-length determinant"]
theorem finiteLengthDeterminant_eq_det
    (φ : Module.End R M) (hM : IsFiniteLength R M) (s : StableCompositionSeries φ) :
    φ.finiteLengthDeterminant hM = s.det := by
  letI : IsNoetherian R M := (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).1
  letI : IsArtinian R M := (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).2
  let h := existsUnique_stableDet φ
  exact (h.choose_spec.1 (someStableCompositionSeries φ hM)).symm.trans (h.choose_spec.1 s)
-- Proof strategy: use `existsUnique_stableDet` to compare the fixed stable series with `s`.

/-- Any stable composition series computes the canonical finite-length trace. -/
@[stacks 0GSY "stable-series formula for the finite-length trace"]
theorem finiteLengthTrace_eq_trace
    (φ : Module.End R M) (hM : IsFiniteLength R M) (s : StableCompositionSeries φ) :
    φ.finiteLengthTrace hM = s.trace := by
  letI : IsNoetherian R M := (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).1
  letI : IsArtinian R M := (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).2
  let h := existsUnique_stableTrace φ
  exact (h.choose_spec.1 (someStableCompositionSeries φ hM)).symm.trans (h.choose_spec.1 s)
-- Proof strategy: use `existsUnique_stableTrace` to compare the fixed stable series with `s`.

/-- Any stable composition series computes the canonical finite-length characteristic
polynomial. -/
@[stacks 0GSY "stable-series formula for the finite-length characteristic polynomial"]
theorem finiteLengthCharpoly_eq_charpoly
    (φ : Module.End R M) (hM : IsFiniteLength R M) (s : StableCompositionSeries φ) :
    φ.finiteLengthCharpoly hM = s.charpoly := by
  letI : IsNoetherian R M := (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).1
  letI : IsArtinian R M := (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).2
  let h := existsUnique_stableCharpoly φ
  exact (h.choose_spec.1 (someStableCompositionSeries φ hM)).symm.trans (h.choose_spec.1 s)
-- Proof strategy: use `existsUnique_stableCharpoly` to compare the fixed stable series with `s`.

end LocalRing

end Module.End

section ShortExact

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {S : ShortComplex (ModuleCat.{v} R)}
variable (φ₁ : Module.End R S.X₁) (φ₂ : Module.End R S.X₂) (φ₃ : Module.End R S.X₃)
variable (hX₁ : IsFiniteLength R S.X₁) (hX₂ : IsFiniteLength R S.X₂)
variable (hX₃ : IsFiniteLength R S.X₃)

namespace Module.End

/-- The finite-length determinant is multiplicative in a compatible short exact sequence. -/
@[stacks 0GSY "Lemma 15.121.1 (1): determinant multiplicativity"]
theorem finiteLengthDeterminant_eq_mul_of_shortExact
    (hS : S.ShortExact)
    (hf : CommSq (ofHom φ₁) S.f (S.f) (ofHom φ₂))
    (hg : CommSq (ofHom φ₂) S.g (S.g) (ofHom φ₃)) :
    φ₂.finiteLengthDeterminant hX₂ =
      φ₁.finiteLengthDeterminant hX₁ * φ₃.finiteLengthDeterminant hX₃ := sorry
-- Proof strategy: choose stable composition series for the outer endomorphisms, splice them
-- through the compatible short exact row to a stable series for `φ₂`, and reduce all three values
-- with `finiteLengthDeterminant_eq_det`; the spliced factor product splits into the two outer
-- products.

/-- The finite-length trace is additive in a compatible short exact sequence. -/
@[stacks 0GSY "Lemma 15.121.1 (2): trace additivity"]
theorem finiteLengthTrace_eq_add_of_shortExact
    (hS : S.ShortExact)
    (hf : CommSq (ofHom φ₁) S.f (S.f) (ofHom φ₂))
    (hg : CommSq (ofHom φ₂) S.g (S.g) (ofHom φ₃)) :
    φ₂.finiteLengthTrace hX₂ =
      φ₁.finiteLengthTrace hX₁ + φ₃.finiteLengthTrace hX₃ := sorry
-- Proof strategy: use the same compatible spliced stable series as for determinant, reduce with
-- `finiteLengthTrace_eq_trace`, and split the finite sum of factor traces at the splice point.

/-- The finite-length characteristic polynomial is multiplicative in a compatible short exact
sequence. -/
@[stacks 0GSY "Lemma 15.121.1 (3): characteristic-polynomial multiplicativity"]
theorem finiteLengthCharpoly_eq_mul_of_shortExact
    (hS : S.ShortExact)
    (hf : CommSq (ofHom φ₁) S.f (S.f) (ofHom φ₂))
    (hg : CommSq (ofHom φ₂) S.g (S.g) (ofHom φ₃)) :
    φ₂.finiteLengthCharpoly hX₂ =
      φ₁.finiteLengthCharpoly hX₁ * φ₃.finiteLengthCharpoly hX₃ := sorry
-- Proof strategy: splice compatible stable composition series across the short exact row, rewrite
-- with `finiteLengthCharpoly_eq_charpoly`, and split the product of factor characteristic
-- polynomials into the two outer products.

end Module.End

end ShortExact

end
