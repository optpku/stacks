/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FiniteFreeModuleResolution
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
noncomputable section
universe u

namespace FiniteProjectiveComplexReplacement
variable (S : Type u) [Ring S]
variable (K : ChainComplex (ModuleCat.{u} S) ℕ)

/-- One explicit free-stage construction, retaining its actual map to K and
its outgoing differential. This is internal algorithmic data, not an assumed comparison package. -/
structure Stage (n : ℕ) where
  P : ModuleCat.{u} S
  previous : ModuleCat.{u} S
  d : P ⟶ previous
  ε : P ⟶ K.X n
  projective : Projective P

/-- Begin with the free module on the actual degree-zero vectors. -/
def initial : Stage S K 0 where
  P := FiniteFreeModuleResolution.free S (K.X 0)
  previous := 0
  d := 0
  ε := FiniteFreeModuleResolution.evaluation S (K.X 0)
  projective := by
    change Projective (ModuleCat.of S ((K.X 0) →₀ S))
    infer_instance

/-- A next-stage generator is a source vector x and a preceding cycle y
whose specified images agree: d_K x = ε y and d_P y = 0. -/
def constraint (n : ℕ) (s : Stage S K n) : Submodule S ((K.X (n + 1)) × s.P) where
  carrier := {p | (K.d (n + 1) n).hom p.1 = s.ε.hom p.2 ∧ s.d.hom p.2 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq
    exact ⟨by simpa only [Prod.fst_add, Prod.snd_add, map_add, hp.1, hq.1],
      by simpa only [Prod.snd_add, map_add, hp.2, hq.2, add_zero]⟩
  smul_mem' := by
    intro a p hp
    exact ⟨by simpa only [Prod.smul_fst, Prod.smul_snd, map_smul, hp.1],
      by simpa only [Prod.smul_snd, map_smul, hp.2, smul_zero]⟩

/-- Freely generate those actual compatible pairs. The two projections give
the next differential and augmentation component, respectively. -/
def step (n : ℕ) (s : Stage S K n) : Stage S K (n + 1) where
  P := FiniteFreeModuleResolution.free S (ModuleCat.of S (constraint S K n s))
  previous := s.P
  d := FiniteFreeModuleResolution.evaluation S (ModuleCat.of S (constraint S K n s)) ≫
    ModuleCat.ofHom ((LinearMap.snd S (K.X (n + 1)) s.P).domRestrict (constraint S K n s))
  ε := FiniteFreeModuleResolution.evaluation S (ModuleCat.of S (constraint S K n s)) ≫
    ModuleCat.ofHom ((LinearMap.fst S (K.X (n + 1)) s.P).domRestrict (constraint S K n s))
  projective := by
    change Projective (ModuleCat.of S ((constraint S K n s) →₀ S))
    infer_instance

/-- The differential sends a compatible-pair generator to its preceding cycle. -/
theorem step_d_single (n : ℕ) (s : Stage S K n) (p : constraint S K n s) :
    (step S K n s).d.hom (Finsupp.single p 1) = p.val.2 := by
  change (Finsupp.linearCombination S (fun q : constraint S K n s => q)
    (Finsupp.single p 1)).val.2 = p.val.2
  rw [Finsupp.linearCombination_single, one_smul]

/-- The augmentation sends a compatible-pair generator to its original vector. -/
theorem step_ε_single (n : ℕ) (s : Stage S K n) (p : constraint S K n s) :
    (step S K n s).ε.hom (Finsupp.single p 1) = p.val.1 := by
  change (Finsupp.linearCombination S (fun q : constraint S K n s => q)
    (Finsupp.single p 1)).val.1 = p.val.1
  rw [Finsupp.linearCombination_single, one_smul]

/-- Deterministic kernel/free recursion for the whole chain complex. -/
def stages : (n : ℕ) → Stage S K n
  | 0 => initial S K
  | n + 1 => step S K n (stages n)

/-- The actual degreewise free terms. -/
abbrev terms (n : ℕ) := (stages S K n).P

/-- The actual compatible-pair projection differentials. -/
def differential (n : ℕ) : terms S K (n + 1) ⟶ terms S K n := (stages S K (n + 1)).d

/-- Successive differentials compose to zero by the cycle constraint. -/
theorem differential_squared (n : ℕ) :
    differential S K (n + 1) ≫ differential S K n = 0 := by
  apply ModuleCat.hom_ext
  ext x
  exact (FiniteFreeModuleResolution.evaluation S
    (ModuleCat.of S (constraint S K (n + 1) (stages S K (n + 1)))) x).property.2

/-- Concrete projective replacement complex; no arbitrary resolution is selected. -/
def complex := ChainComplex.of (terms S K) (differential S K) (differential_squared S K)

/-- The replacement map uses the actual vector projections of the recursion. -/
def toOriginal : complex S K ⟶ K where
  f n := (stages S K n).ε
  comm' := by
    intro i j hij
    have hij' : j + 1 = i := hij
    subst i
    change (stages S K (j + 1)).ε ≫ K.d (j + 1) j =
      ChainComplex.of.d (terms S K) (differential S K) (j + 1) j ≫ (stages S K j).ε
    rw [ChainComplex.of_d]
    apply ModuleCat.hom_ext
    ext x
    exact (FiniteFreeModuleResolution.evaluation S
      (ModuleCat.of S (constraint S K j (stages S K j))) x).property.1

/-- Cycle lifts and lifts of cycles over boundaries give an isomorphism on homology. -/
private theorem quasiIso_of_lifts {A B : ShortComplex (ModuleCat.{u} S)} (φ : A ⟶ B)
    (hsurj : ∀ x : B.X₂, B.g x = 0 →
      ∃ y : A.X₂, A.g y = 0 ∧ φ.τ₂ y = x)
    (hinj : ∀ y : A.X₂, A.g y = 0 →
      ∀ x : B.X₁, B.f x = φ.τ₂ y → ∃ z : A.X₁, A.f z = y) :
    ShortComplex.QuasiIso φ := by
  haveI : Epi (ShortComplex.cyclesMap φ) := by
    apply (ModuleCat.epi_iff_surjective _).2
    intro z
    obtain ⟨y, hy, hφy⟩ := hsurj (B.iCycles z)
      (congrArg (fun f : B.cycles ⟶ B.X₃ => f.hom z) B.iCycles_g)
    let w := A.moduleCatCyclesIso.inv ⟨y, hy⟩
    refine ⟨w, ?_⟩
    apply (ModuleCat.mono_iff_injective B.iCycles).1 inferInstance
    calc
      B.iCycles (ShortComplex.cyclesMap φ w) = φ.τ₂ (A.iCycles w) :=
        congrArg (fun f : A.cycles ⟶ B.X₂ => f.hom w) (ShortComplex.cyclesMap_i φ)
      _ = φ.τ₂ y := congrArg φ.τ₂
        (congrArg (fun f : A.moduleCatLeftHomologyData.K ⟶ A.X₂ => f.hom ⟨y, hy⟩)
          A.moduleCatCyclesIso_inv_iCycles)
      _ = B.iCycles z := hφy
  haveI : Mono (ShortComplex.homologyMap φ) := by
    apply (ModuleCat.mono_iff_ker_eq_bot _).2
    apply le_antisymm ?_ bot_le
    intro h hh
    change (ShortComplex.homologyMap φ).hom h = 0 at hh
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective A.homologyπ).1 inferInstance h
    have hz : B.homologyπ (ShortComplex.cyclesMap φ z) = 0 :=
      (congrArg (fun f : A.cycles ⟶ B.homology => f.hom z)
        (ShortComplex.homologyπ_naturality φ)).symm.trans hh
    have hp : B.pOpcycles (φ.τ₂ (A.iCycles z)) = 0 := by
      calc
        B.pOpcycles (φ.τ₂ (A.iCycles z)) =
            B.pOpcycles (B.iCycles (ShortComplex.cyclesMap φ z)) :=
          congrArg B.pOpcycles
            (congrArg (fun f : A.cycles ⟶ B.X₂ => f.hom z)
              (ShortComplex.cyclesMap_i φ)).symm
        _ = B.homologyι (B.homologyπ (ShortComplex.cyclesMap φ z)) :=
          (congrArg (fun f : B.cycles ⟶ B.opcycles =>
            f.hom (ShortComplex.cyclesMap φ z)) B.homology_π_ι).symm
        _ = 0 := by rw [hz]; exact map_zero _
    obtain ⟨x, hx⟩ := (B.moduleCat_pOpcycles_eq_zero_iff _).1 hp
    obtain ⟨y, hy⟩ := hinj (A.iCycles z)
      (congrArg (fun f : A.cycles ⟶ A.X₃ => f.hom z) A.iCycles_g) x hx
    have hy' : A.toCycles y = z := by
      apply (ModuleCat.mono_iff_injective A.iCycles).1 inferInstance
      exact (congrArg (fun f : A.X₁ ⟶ A.X₂ => f.hom y) A.toCycles_i).trans hy
    change A.homologyπ z = 0
    rw [← hy']
    exact congrArg (fun f : A.X₁ ⟶ A.homology => f.hom y) A.toCycles_comp_homologyπ
  rw [ShortComplex.quasiIso_iff]
  exact isIso_of_mono_of_epi _

/-- Cycles lift via (x,0); null cycles lift via their specified boundary pair.
This proves quasi-isomorphism of this particular chain map. -/
theorem toOriginal_quasiIso : QuasiIso (toOriginal S K) := by
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff]
    apply quasiIso_of_lifts S
    · intro x hx
      refine ⟨Finsupp.single x 1, ?_, ?_⟩
      · change (ChainComplex.of.d (terms S K) (differential S K) 0 0).hom _ = 0
        simp [ChainComplex.of.d]
      · change (FiniteFreeModuleResolution.evaluation S (K.X 0)).hom _ = x
        simp [FiniteFreeModuleResolution.evaluation]
    · intro y hy x hx
      change (K.d 1 0).hom x = (stages S K 0).ε.hom y at hx
      let p : constraint S K 0 (stages S K 0) := ⟨(x, y), hx, rfl⟩
      refine ⟨Finsupp.single p 1, ?_⟩
      change (differential S K 0).hom (Finsupp.single p 1) = y
      exact step_d_single S K 0 (stages S K 0) p
  | succ n =>
    rw [quasiIsoAt_iff' _ (n + 1 + 1) (n + 1) n
      ((ComplexShape.down ℕ).prev_eq' (by rfl))
      ((ComplexShape.down ℕ).next_eq' (by rfl))]
    apply quasiIso_of_lifts S
    · intro x hx
      change (K.d (n + 1) n).hom x = 0 at hx
      let p : constraint S K n (stages S K n) := ⟨(x, 0), by simpa using hx, by simp⟩
      refine ⟨Finsupp.single p 1, ?_, ?_⟩
      · change (ChainComplex.of.d (terms S K) (differential S K) (n + 1) n).hom _ = 0
        rw [ChainComplex.of_d]
        exact step_d_single S K n (stages S K n) p
      · change (stages S K (n + 1)).ε.hom (Finsupp.single p 1) = x
        exact step_ε_single S K n (stages S K n) p
    · intro y hy x hx
      change (ChainComplex.of.d (terms S K) (differential S K) (n + 1) n).hom y = 0 at hy
      rw [ChainComplex.of_d] at hy
      change (K.d (n + 1 + 1) (n + 1)).hom x = (stages S K (n + 1)).ε.hom y at hx
      let p : constraint S K (n + 1) (stages S K (n + 1)) := ⟨(x, y), hx, hy⟩
      refine ⟨Finsupp.single p 1, ?_⟩
      change (ChainComplex.of.d (terms S K) (differential S K) (n + 1 + 1) (n + 1)).hom _ = y
      rw [ChainComplex.of_d]
      exact step_d_single S K (n + 1) (stages S K (n + 1)) p

/-- Every constructed term is free, hence projective in ModuleCat S. -/
theorem term_projective (n : ℕ) : Projective ((complex S K).X n) := (stages S K n).projective

/-- For a finite coefficient ring and finite original terms, the compatible
pair submodules and free stages remain finite. No claim is made for arbitrary resolutions. -/
theorem term_finite [Finite S] (hfin : ∀ n : ℕ, Finite (K.X n)) (n : ℕ) :
    Finite ((complex S K).X n) := by
  change Finite (terms S K n)
  induction n with
  | zero =>
    letI : Finite (K.X 0) := hfin 0
    exact FiniteFreeModuleResolution.free_finite S (K.X 0)
  | succ n hn =>
    letI : Finite (terms S K n) := hn
    letI : Finite (K.X (n + 1)) := hfin (n + 1)
    letI : Finite (ModuleCat.of S (constraint S K n (stages S K n))) := by
      change Finite (constraint S K n (stages S K n))
      infer_instance
    exact FiniteFreeModuleResolution.free_finite S _

end FiniteProjectiveComplexReplacement
