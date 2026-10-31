/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import ReasLib.Algebra.Module.ClosedPointFiber
import Mathlib.Tactic.CrossRefAttribute

/-!
# Visible quotients of closed-point module fibers

This leaf owns the canonical quotient `V(x)` of a closed-point fiber by the vectors invisible to
global linear forms.  It also records the short exact sequence defining `V(x)` and the localized
splitting criterion for finitely presented modules.

@stack 0GV9
-/

@[expose] public section

open scoped ClosedPointFiber

universe u v

namespace Module.ClosedFiber

variable {R : Type u} [CommRing R]

/-- The composite `N → R → R / x` underlying the fiberwise linear form induced by
`φ : Module.Dual R N`. -/
@[stacks 0GV9 "quotient linear form over the base ring"]
noncomputable def quotientLinearFormBase
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) (φ : Module.Dual R N) :
    N →ₗ[R] R ⧸ x.1.asIdeal :=
  (Ideal.Quotient.mkₐ R x.1.asIdeal).toLinearMap.comp φ

/-- The ideal multiple `xN` lies in the kernel of the quotient-valued form induced by `φ`. -/
theorem smulTop_le_ker_quotientLinearFormBase
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) (φ : Module.Dual R N) :
    x.1.asIdeal • (⊤ : Submodule R N) ≤
      LinearMap.ker (quotientLinearFormBase N x φ) := by
  intro z hz
  refine Submodule.smul_induction_on hz ?_ ?_
  · intro r hr n hn
    change Ideal.Quotient.mk x.1.asIdeal (φ (r • n)) = 0
    rw [map_smul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right (φ n) x.1.asIdeal hr)
  · intro z₁ z₂ hz₁ hz₂
    rw [LinearMap.mem_ker] at hz₁ hz₂ ⊢
    change (quotientLinearFormBase N x φ) (z₁ + z₂) = 0
    rw [(quotientLinearFormBase N x φ).map_add, hz₁, hz₂, add_zero]

/-- The `R`-linear map on `N(x)` induced by a global linear form, before transporting the target
from `R / x` to `κ(x)`. -/
@[stacks 0GV9 "quotient linear form on the closed-point fiber"]
noncomputable def quotientLinearFormMap
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) (φ : Module.Dual R N) :
    N﹙x﹚ →ₗ[R] R ⧸ x.1.asIdeal :=
  (x.1.asIdeal • (⊤ : Submodule R N)).liftQ
    (quotientLinearFormBase N x φ)
    (smulTop_le_ker_quotientLinearFormBase N x φ)

/-- The quotient-valued fiber form respects the `R / x`-scalar action. -/
theorem quotientLinearFormMap_map_smul
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) (φ : Module.Dual R N)
    (c : R ⧸ x.1.asIdeal) (q : N﹙x﹚) :
    quotientLinearFormMap N x φ (c • q) = c • quotientLinearFormMap N x φ q := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine Submodule.Quotient.induction_on (x.1.asIdeal • (⊤ : Submodule R N)) q ?_
  intro n
  rw [Module.Quotient.mk_smul_mk]
  change Ideal.Quotient.mk x.1.asIdeal (φ (r • n)) = _
  simp [quotientLinearFormMap, quotientLinearFormBase, Submodule.liftQ_apply,
    map_smul, smul_eq_mul]

/-- A global `R`-linear form induces an `(R / x)`-linear form on the quotient fiber. -/
@[stacks 0GV9 "quotient-valued closed-point fiber form"]
noncomputable def quotientLinearForm
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) (φ : Module.Dual R N) :
    Module.Dual (R ⧸ x.1.asIdeal) (N﹙x﹚) :=
  { toFun := quotientLinearFormMap N x φ
    map_add' := (quotientLinearFormMap N x φ).map_add
    map_smul' := quotientLinearFormMap_map_smul N x φ }

/-- Additivity of the residue-field-valued form induced on the closed-point fiber. -/
theorem linearForm_map_add
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) (φ : Module.Dual R N) (a b : N﹙x﹚) :
    residueFieldAlgEquiv (R := R) x (quotientLinearForm N x φ (a + b)) =
      residueFieldAlgEquiv (R := R) x (quotientLinearForm N x φ a) +
        residueFieldAlgEquiv (R := R) x (quotientLinearForm N x φ b) := by
  rw [map_add, map_add]

/-- Compatibility of the induced fiber form with the `κ(x)`-scalar action. -/
theorem linearForm_map_smul
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) (φ : Module.Dual R N)
    (c : κ(x)) (q : N﹙x﹚) :
    residueFieldAlgEquiv (R := R) x (quotientLinearForm N x φ (c • q)) =
      c • residueFieldAlgEquiv (R := R) x (quotientLinearForm N x φ q) := by
  obtain ⟨c', rfl⟩ := (residueFieldAlgEquiv (R := R) x).surjective c
  dsimp [instModule]
  change residueFieldAlgEquiv (R := R) x
      (quotientLinearFormMap N x φ
        ((residueFieldAlgEquiv (R := R) x).symm
          ((residueFieldAlgEquiv (R := R) x) c') • q)) = _
  rw [(residueFieldAlgEquiv (R := R) x).symm_apply_apply]
  rw [quotientLinearFormMap_map_smul]
  simp only [smul_eq_mul, map_mul]
  rfl

/-- The `κ(x)`-linear form on `N(x)` induced by a global `R`-linear form. -/
@[stacks 0GV9 "canonical closed-point fiber linear form"]
noncomputable def linearForm
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) (φ : Module.Dual R N) :
    Module.Dual κ(x) (N﹙x﹚) :=
  { toFun := fun q ↦ residueFieldAlgEquiv (R := R) x (quotientLinearForm N x φ q)
    map_add' := linearForm_map_add N x φ
    map_smul' := linearForm_map_smul N x φ }

/-- The invisible subspace `B(x)` is the common kernel of all fiberwise forms induced by global
`R`-linear forms. -/
@[stacks 0GV9 "invisible closed-point fiber subspace"]
noncomputable abbrev invisible
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) : Submodule κ(x) (N﹙x﹚) :=
  (Submodule.span κ(x) (Set.range (linearForm N x))).dualCoannihilator

scoped[ClosedPointFiber] notation:max "B(" x:max ")" =>
  Module.ClosedFiber.invisible _ x

/-- The visible fiber `V(x)` is the quotient of `N(x)` by its invisible subspace. -/
@[stacks 0GV9 "visible closed-point fiber quotient"]
noncomputable abbrev Visible
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) : Type v :=
  N﹙x﹚ ⧸ invisible N x

scoped[ClosedPointFiber] notation:max "V(" x:max ")" =>
  Module.ClosedFiber.Visible _ x

/-- The inclusion of `B(x)` into the full fiber `N(x)`. -/
@[stacks 0GV9 "invisible subspace inclusion"]
noncomputable def inclusion
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) :
    invisible N x →ₗ[κ(x)] N﹙x﹚ :=
  (invisible N x).subtype

/-- The quotient map from `N(x)` to its visible quotient `V(x)`. -/
@[stacks 0GV9 "visible fiber quotient map"]
noncomputable def quotientMap
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) :
    N﹙x﹚ →ₗ[κ(x)] Visible N x :=
  (invisible N x).mkQ

/-- The defining inclusion and quotient maps of the visible fiber have zero composite. -/
theorem quotientMap_comp_inclusion
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) :
    (quotientMap N x).comp (inclusion N x) = 0 := by
  ext q
  change (invisible N x).mkQ ((invisible N x).subtype q) = 0
  exact (Submodule.Quotient.mk_eq_zero _).2 q.property

/-- The canonical short complex `B(x) ⟶ N(x) ⟶ V(x)`. -/
@[stacks 0GV9 "canonical visible-fiber short complex"]
noncomputable abbrev sequence
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) :
    CategoryTheory.ShortComplex (ModuleCat.{v} κ(x)) :=
  CategoryTheory.ShortComplex.moduleCatMk (inclusion N x) (quotientMap N x)
    (quotientMap_comp_inclusion N x)

/-- Lemma 15.128.2 (1), tag 0GV9: the canonical sequence
`0 ⟶ B(x) ⟶ N(x) ⟶ V(x) ⟶ 0` is short exact. -/
@[stacks 0GV9 "canonical visible-fiber short exact sequence"]
theorem shortExact
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) : (sequence N x).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · intro q
    constructor
    · intro hq
      change (invisible N x).mkQ q = 0 at hq
      exact ⟨⟨q, (Submodule.Quotient.mk_eq_zero _).1 hq⟩, rfl⟩
    · rintro ⟨q, rfl⟩
      change (invisible N x).mkQ ((invisible N x).subtype q) = 0
      exact (Submodule.Quotient.mk_eq_zero _).2 q.property
  · exact (invisible N x).injective_subtype
  · exact (invisible N x).mkQ_surjective

/-- The class in `V(x)` represented by the image of a global section in `N(x)`. -/
@[stacks 0GV9 "visible class of a global section"]
noncomputable abbrev visibleClass
    {N : Type v} [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) (s : N) : Visible N x :=
  quotientMap N x (Module.ClosedFiber.mk x s)

/-- Every visible class at a closed point is represented by a global section. -/
theorem visibleClass_surjective
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) :
    Function.Surjective (visibleClass x : N → Visible N x) := by
  intro y
  obtain ⟨q, rfl⟩ := (invisible N x).mkQ_surjective y
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective (x.1.asIdeal • (⊤ : Submodule R N)) q
  exact ⟨s, rfl⟩

/-- Every global form vanishes on the invisible subspace of the fiber. -/
theorem invisible_le_ker_linearForm
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) (φ : Module.Dual R N) :
    invisible N x ≤ LinearMap.ker (linearForm N x φ) := by
  intro q hq
  change q ∈ (Submodule.span κ(x) (Set.range (linearForm N x))).dualCoannihilator at hq
  rw [Submodule.mem_dualCoannihilator] at hq
  exact hq (linearForm N x φ) (Submodule.subset_span ⟨φ, rfl⟩)

/-- The linear form on `V(x)` induced by a global `R`-linear form. -/
@[stacks 0GV9 "visible quotient linear form"]
noncomputable def visibleLinearForm
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) (φ : Module.Dual R N) :
    Module.Dual κ(x) (Visible N x) :=
  (invisible N x).liftQ (linearForm N x φ) (invisible_le_ker_linearForm N x φ)

/-- Evaluation of an induced visible-fiber form on the class of a global section. -/
theorem visibleLinearForm_apply_visibleClass
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) (φ : Module.Dual R N) (s : N) :
    visibleLinearForm N x φ (visibleClass x s) = algebraMap R κ(x) (φ s) := by
  change residueFieldAlgEquiv (R := R) x
      ((x.1.asIdeal • (⊤ : Submodule R N)).liftQ (quotientLinearFormBase N x φ)
        (smulTop_le_ker_quotientLinearFormBase N x φ) (Submodule.Quotient.mk s)) = _
  rw [Submodule.liftQ_apply]
  change residueFieldAlgEquiv (R := R) x
      (algebraMap R (R ⧸ x.1.asIdeal) (φ s)) = _
  exact Ideal.ResidueField.quotientAlgEquiv_apply_algebraMap x.1.asIdeal (φ s)

/-- For a finitely presented module, every linear form on `V(x)` is induced by a global
`R`-linear form. -/
@[stacks 0GV9 "surjectivity of global forms onto the visible dual"]
theorem visibleLinearForm_surjective
    (N : Type v) [AddCommGroup N] [Module R N] [Module.FinitePresentation R N]
    (x : closedPoints (PrimeSpectrum R)) :
    Function.Surjective (visibleLinearForm N x) := by
  letI := finiteDimensional_of_finitePresentation N x
  letI : FiniteDimensional κ(x) (Visible N x) :=
    Module.Finite.of_surjective (quotientMap N x) (invisible N x).mkQ_surjective
  have hspan : Submodule.span κ(x) (Set.range (visibleLinearForm N x)) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro q hq
    obtain ⟨p, rfl⟩ := (invisible N x).mkQ_surjective q
    by_contra h
    push Not at h
    have hp : p ∈ invisible N x := by
      change p ∈ ((Submodule.span κ(x) (Set.range (linearForm N x))).dualCoannihilator :
        Set (N﹙x﹚))
      rw [Submodule.coe_dualCoannihilator_span]
      rintro _ ⟨φ, rfl⟩
      exact h _ ⟨φ, rfl⟩
    exact hq ((Submodule.Quotient.mk_eq_zero _).2 hp)
  intro ℓ
  have hℓ : ℓ ∈ Submodule.span κ(x) (Set.range (visibleLinearForm N x)) := by
    rw [hspan]
    exact Submodule.mem_top
  induction hℓ using Submodule.span_induction with
  | mem f hf => exact hf
  | zero =>
      refine ⟨0, ?_⟩
      apply LinearMap.ext
      intro q
      obtain ⟨s, rfl⟩ := visibleClass_surjective N x q
      simp [visibleLinearForm_apply_visibleClass]
  | add f g hf hg ihf ihg =>
      obtain ⟨φ, rfl⟩ := ihf
      obtain ⟨ψ, rfl⟩ := ihg
      refine ⟨φ + ψ, ?_⟩
      apply LinearMap.ext
      intro q
      obtain ⟨s, rfl⟩ := visibleClass_surjective N x q
      simp [visibleLinearForm_apply_visibleClass]
  | smul c f hf ih =>
      obtain ⟨φ, rfl⟩ := ih
      obtain ⟨r, rfl⟩ := x.1.asIdeal.algebraMap_residueField_surjective c
      refine ⟨r • φ, ?_⟩
      apply LinearMap.ext
      intro q
      obtain ⟨s, rfl⟩ := visibleClass_surjective N x q
      change (visibleLinearForm N x (r • φ)) (visibleClass x s) =
        (algebraMap R κ(x) r) • (visibleLinearForm N x φ) (visibleClass x s)
      rw [visibleLinearForm_apply_visibleClass, visibleLinearForm_apply_visibleClass]
      change algebraMap R κ(x) (r * φ s) =
        (algebraMap R κ(x) r) * algebraMap R κ(x) (φ s)
      rw [map_mul]

/-- The `R`-linear map sending the standard basis of `R^r` to a selected family of sections. -/
@[stacks 0GV9 "linear map of selected sections"]
noncomputable abbrev selectedSectionsMap
    {N : Type v} [AddCommGroup N] [Module R N]
    {r : ℕ} (s : Fin r → N) : (Fin r → R) →ₗ[R] N :=
  (Pi.basisFun R (Fin r)).constr R s

/-- The selected sections split after inverting an element away from `x` when their localized map
admits a left inverse. -/
@[stacks 0GV9 "selected sections split after localization"]
def SelectedSectionsSplitAfterInverting
    {N : Type v} [AddCommGroup N] [Module R N]
    {r : ℕ} (x : closedPoints (PrimeSpectrum R)) (s : Fin r → N) : Prop :=
  ∃ f : R, f ∉ x.1.asIdeal ∧
    ∃ ρ : LocalizedModule.Away f N →ₗ[Localization.Away f]
        LocalizedModule.Away f (Fin r → R),
      Function.LeftInverse ρ
        (LocalizedModule.map (Submonoid.powers f) (selectedSectionsMap s))

/-- Lemma 15.128.2 (2), tag 0GV9: selected sections split off a free summand after localization
away from `x` exactly when their classes in `V(x)` are linearly independent. -/
@[stacks 0GV9 "localized splitting and visible-class independence"]
theorem selectedSectionsSplitAfterInverting_iff_linearIndependent
    {N : Type v} [AddCommGroup N] [Module R N] [Module.FinitePresentation R N]
    (x : closedPoints (PrimeSpectrum R)) {r : ℕ} (s : Fin r → N) :
    SelectedSectionsSplitAfterInverting x s ↔
      LinearIndependent κ(x) (visibleClass x ∘ s) := sorry
-- Proof strategy: a localized left inverse yields coordinate forms whose reductions separate the
-- visible classes. Conversely extend the independent visible classes to coordinate forms, lift
-- them globally using `visibleLinearForm_surjective`, and invert one element outside `x` so the
-- resulting matrix identities give a left inverse to the localized selected-sections map.

end Module.ClosedFiber
