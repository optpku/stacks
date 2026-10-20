/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flatness.LocalCriterion
public import stacks_project.Chap10.Lemma_10_110_3.IdealCoordinate
public import stacks_project.Chap10.Lemma_10_110_3.KoszulFirstOrder
public import stacks_project.Chap10.Lemma_10_110_3.MinimalResolution
public import ReasLib.LinearAlgebra.QuotientByIdeal.Tensor

/-!
# Minimal-comparison support for Lemma 10.110.3

@stack 00OA
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

local notation "moduleSingle[" R "]" M =>
  CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M)

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: an `R`-linear map to the residue field kills the
maximal-ideal multiple of any source module. -/
lemma linearMap_to_residueField_eq_zero_of_mem_maximal_smul_top
    {M : Type u} [AddCommGroup M] [Module R M]
    (f : M →ₗ[R] ResidueField R) {y : M}
    (hy : y ∈ maximalIdeal R • (⊤ : Submodule R M)) :
    f y = 0 := by
  -- Induct over the `𝔪`-linear-combination presentation and use that the residue action of
  -- every element of `𝔪` is zero.
  refine Submodule.smul_induction_on hy ?_ ?_
  · intro r hr y _hy
    have hr0 : algebraMap R (ResidueField R) r = 0 := by
      simpa [IsLocalRing.ResidueField.algebraMap_eq] using
        (IsLocalRing.residue_eq_zero_iff (R := R) r).mpr hr
    calc
      f (r • y) = r • f y := map_smul f r y
      _ = (algebraMap R (ResidueField R) r) * f y := Algebra.smul_def r (f y)
      _ = 0 := by rw [hr0, zero_mul]
  · intro y z hy hz
    simp [hy, hz]

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: in degree zero, vanishing in the residue field puts an
exterior-power element in the maximal-ideal multiple. -/
lemma exteriorPower_zero_mem_maximal_smul_top_of_quotient_eq_zero
    {E : Type u} [AddCommGroup E] [Module R E]
    {z : ⋀[R]^0 E}
    (hz : ((Ideal.Quotient.mkₐ R (maximalIdeal R)).toLinearMap)
      ((exteriorPower.zeroEquiv R E) z) = 0) :
    z ∈ maximalIdeal R • (⊤ : Submodule R (⋀[R]^0 E)) := by
  let r : R := (exteriorPower.zeroEquiv R E) z
  -- The degree-zero exterior-power equivalence identifies the kernel with `𝔪 ⊂ R`, then the
  -- element is written as an `𝔪`-multiple of the unit basis vector.
  have hr : r ∈ maximalIdeal R := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact hz
  have hz_eq : z = r • (exteriorPower.zeroEquiv R E).symm (1 : R) := by
    rw [← LinearEquiv.map_smul]
    simp [r]
  rw [hz_eq]
  exact Submodule.smul_mem_smul hr trivial

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: the degree-zero component of a Koszul comparison is
injective after reducing modulo the maximal ideal. -/
lemma minimalComparison_reducedComponent_zero_injective
    {n : ℕ} (x : Fin n → maximalIdeal R)
    {F : ChainComplex (ModuleCat R) ℕ}
    (ρ : F ⟶ moduleSingle[R] (ResidueField R))
    (α : localKoszulComplexOn (R := R) (fun i ↦ (x i : R)) ⟶ F)
    (hα : α ≫ ρ = localKoszulAugmentation (R := R) x) :
    Function.Injective (((α.f 0).hom).quotientMapByIdeal (maximalIdeal R)) := sorry

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: a minimal displayed target differential sends the first
maximal-ideal layer into the square layer in owner chain-complex coordinates. -/
lemma minimalTarget_ownerDifferential_mem_maximalSquare
    {d : ℕ} (C : FiniteFreeComplex R (d + 1))
    (hminimal :
      ∀ i : Fin (d + 1), ∀ a : Fin (C.rank i.succ), ∀ b : Fin (C.rank i.castSucc),
        FiniteFreeComplex.diffEntry C i a b ∈ maximalIdeal R)
    {i : ℕ} (hi : i < d + 2) {y : C.toChainComplex.X (i + 1)}
    (hy : y ∈ maximalIdeal R • (⊤ : Submodule R (C.toChainComplex.X (i + 1)))) :
    ((C.toChainComplex.d (i + 1) i).hom y) ∈
      (maximalIdeal R) ^ 2 • (⊤ : Submodule R (C.toChainComplex.X i)) := sorry

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: the top component of a minimal Koszul comparison is
injective after reducing modulo the maximal ideal. -/
lemma minimalComparison_topQuotientMap_injective
    {d : ℕ}
    (b : Module.Basis (Fin (d + 2)) (ResidueField R) (CotangentSpace R))
    (x : Fin (d + 2) → maximalIdeal R)
    (hx : ∀ i, (maximalIdeal R).toCotangent (x i) = b i)
    (C : FiniteFreeComplex R (d + 1))
    (ρ : C.toChainComplex ⟶ moduleSingle[R] (ResidueField R))
    (hρ : ChainComplex.IsFiniteFreeResolution ρ)
    (α : localKoszulComplexOn (R := R) (fun i ↦ (x i : R)) ⟶ C.toChainComplex)
    (hα : α ≫ ρ = localKoszulAugmentation (R := R) x)
    (hminimal :
      ∀ i : Fin (d + 1), ∀ a : Fin (C.rank i.succ), ∀ b : Fin (C.rank i.castSucc),
        FiniteFreeComplex.diffEntry C i a b ∈ maximalIdeal R) :
    Function.Injective
      (((α.f (d + 2)).hom).quotientMapByIdeal (maximalIdeal R)) := sorry

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: the residue-field base change of the top Koszul
comparison component is injective for cotangent-basis lifts and a minimal target resolution. -/
lemma minimalComparison_topBaseChange_injective
    {d : ℕ}
    (b : Module.Basis (Fin (d + 2)) (ResidueField R) (CotangentSpace R))
    (x : Fin (d + 2) → maximalIdeal R)
    (hx : ∀ i, (maximalIdeal R).toCotangent (x i) = b i)
    (C : FiniteFreeComplex R (d + 1))
    (ρ : C.toChainComplex ⟶ moduleSingle[R] (ResidueField R))
    (hρ : ChainComplex.IsFiniteFreeResolution ρ)
    (α : localKoszulComplexOn (R := R) (fun i ↦ (x i : R)) ⟶ C.toChainComplex)
    (hα : α ≫ ρ = localKoszulAugmentation (R := R) x)
    (hminimal :
      ∀ i : Fin (d + 1), ∀ a : Fin (C.rank i.succ), ∀ b : Fin (C.rank i.castSucc),
        FiniteFreeComplex.diffEntry C i a b ∈ maximalIdeal R) :
    Function.Injective
      (TensorProduct.map
        (LinearMap.id : ResidueField R →ₗ[R] ResidueField R)
        (α.f (d + 2)).hom :
        TensorProduct R (ResidueField R)
            ((localKoszulComplexOn (R := R) (fun i ↦ (x i : R))).X (d + 2)) →ₗ[R]
      TensorProduct R (ResidueField R) (C.toChainComplex.X (d + 2))) := by
  -- Route correction: the previous top-only contradiction was too weak for arbitrary `x`; the
  -- remaining invariant is the source proof's reduced-component induction with the cotangent-basis
  -- lift and entrywise minimality hypotheses made explicit.
  -- The tensor transport is now isolated in the closed-fiber adapter; the source-facing quotient
  -- injectivity remains the only mathematical input needed at this top degree.
  change Function.Injective ((α.f (d + 2)).hom.lTensor (R ⧸ maximalIdeal R))
  exact (LinearMap.quotientMapByIdeal_injective_iff_lTensor_injective
    (maximalIdeal R) (α.f (d + 2)).hom).mp
      (minimalComparison_topQuotientMap_injective (R := R) b x hx C ρ hρ α hα hminimal)

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: the top first-order Koszul comparison contradicts a
minimal finite free resolution whose top residue-field term is zero. -/
lemma minimalComparison_topFirstOrder_contradiction
    {d : ℕ}
    (b : Module.Basis (Fin (d + 2)) (ResidueField R) (CotangentSpace R))
    (x : Fin (d + 2) → maximalIdeal R)
    (hx : ∀ i, (maximalIdeal R).toCotangent (x i) = b i)
    (C : FiniteFreeComplex R (d + 1))
    (ρ : C.toChainComplex ⟶ moduleSingle[R] (ResidueField R))
    (hρ : ChainComplex.IsFiniteFreeResolution ρ)
    (α : localKoszulComplexOn (R := R) (fun i ↦ (x i : R)) ⟶ C.toChainComplex)
    (hα : α ≫ ρ = localKoszulAugmentation (R := R) x)
    (hminimal :
      ∀ i : Fin (d + 1), ∀ a : Fin (C.rank i.succ), ∀ b : Fin (C.rank i.castSucc),
        FiniteFreeComplex.diffEntry C i a b ∈ maximalIdeal R)
    (htopTerm :
      Nontrivial
        (TensorProduct R (ResidueField R)
          ((localKoszulComplexOn (R := R) (fun i ↦ (x i : R))).X (d + 2))))
    (htarget :
      Subsingleton (TensorProduct R (ResidueField R) (C.toChainComplex.X (d + 2)))) :
    False := by
  -- The only remaining source-facing invariant is injectivity of the top reduced comparison map.
  -- Once that is available, nontriviality of the source transfers a subsingleton contradiction
  -- back from the top target term.
  have hinj :
      Function.Injective
        (TensorProduct.map
          (LinearMap.id : ResidueField R →ₗ[R] ResidueField R)
          (α.f (d + 2)).hom :
          TensorProduct R (ResidueField R)
              ((localKoszulComplexOn (R := R) (fun i ↦ (x i : R))).X (d + 2)) →ₗ[R]
            TensorProduct R (ResidueField R) (C.toChainComplex.X (d + 2))) :=
    minimalComparison_topBaseChange_injective (R := R) b x hx C ρ hρ α hα hminimal
  have hsource_subsingleton :
      Subsingleton
        (TensorProduct R (ResidueField R)
          ((localKoszulComplexOn (R := R) (fun i ↦ (x i : R))).X (d + 2))) := by
    constructor
    intro y z
    exact hinj (htarget.elim _ _)
  exact (not_subsingleton_iff_nontrivial.mpr htopTerm) hsource_subsingleton

end
