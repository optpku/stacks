/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RepresentationTheory.Homological.ContCohomology.DiscreteCochains
public import ReasLib.Algebra.GroupCohomology.ProjectiveLinearBoundary
public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.Topology.LocallyConstant.Basic

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Action CategoryTheory.Action.ModuleCat

namespace GaloisCohomology

variable (K : Type u) (Ksep : Type v) [Field K] [Field Ksep]
variable [Algebra K Ksep] [IsSepClosure K Ksep]

/-- The identity Galois automorphism induces the identity integral linear endomorphism of units. -/
theorem unitsAction_map_one :
    ModuleCat.ofHom
      ((MulDistribMulAction.toMonoidHom (A := Ksepˣ) (1 : Gal(Ksep / K))).toAdditive.toIntLinearMap) =
        (1 : End (ModuleCat.of ℤ (Additive Ksepˣ))) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change Additive.ofMul ((1 : Gal(Ksep / K)) • (Additive.toMul x : Ksepˣ)) = x
  rw [one_smul]
  rfl

/-- Composition of Galois automorphisms induces composition of integral linear maps on units. -/
theorem unitsAction_map_mul (σ τ : Gal(Ksep / K)) :
    ModuleCat.ofHom
      ((MulDistribMulAction.toMonoidHom (A := Ksepˣ) (σ * τ)).toAdditive.toIntLinearMap) =
      ModuleCat.ofHom
        ((MulDistribMulAction.toMonoidHom (A := Ksepˣ) τ).toAdditive.toIntLinearMap) ≫
      ModuleCat.ofHom
        ((MulDistribMulAction.toMonoidHom (A := Ksepˣ) σ).toAdditive.toIntLinearMap) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change Additive.ofMul ((σ * τ) • (Additive.toMul x : Ksepˣ)) =
    Additive.ofMul (σ • (τ • (Additive.toMul x : Ksepˣ)))
  exact congrArg Additive.ofMul (mul_smul σ τ (Additive.toMul x : Ksepˣ))

/-- The integral linear action of the absolute Galois group on separable-closure units. -/
noncomputable def unitsAction : Gal(Ksep / K) →* End (ModuleCat.of ℤ (Additive Ksepˣ)) where
  toFun σ := ModuleCat.ofHom
    ((MulDistribMulAction.toMonoidHom (A := Ksepˣ) σ).toAdditive.toIntLinearMap)
  map_one' := unitsAction_map_one K Ksep
  map_mul' := unitsAction_map_mul K Ksep

/-- Every separable-closure unit has open stabilizer for the canonical Galois action. -/
theorem unitsAction_openStabilizer :
    openStabilizer ℤ (Gal(Ksep / K))
      { V := ModuleCat.of ℤ (Additive Ksepˣ), ρ := unitsAction K Ksep } := by
  intro x
  change IsOpen {σ : Gal(Ksep / K) |
    σ • (Additive.toMul x : Ksepˣ) = (Additive.toMul x : Ksepˣ)}
  have h : {σ : Gal(Ksep / K) |
      σ • (Additive.toMul x : Ksepˣ) = (Additive.toMul x : Ksepˣ)} =
      (MulAction.stabilizer (Gal(Ksep / K))
        ((Additive.toMul x : Ksepˣ) : Ksep) : Set (Gal(Ksep / K))) := by
    ext σ
    exact Units.ext_iff
  rw [h]
  exact stabilizer_isOpen_of_isIntegral (K := K) ((Additive.toMul x : Ksepˣ) : Ksep)

/-- The discrete integral Galois module of separable-closure units, viewed additively. -/
noncomputable def unitsModule : DiscreteModuleCat ℤ (Gal(Ksep / K)) :=
  ⟨{ V := ModuleCat.of ℤ (Additive Ksepˣ), ρ := unitsAction K Ksep },
    unitsAction_openStabilizer K Ksep⟩

/-- The underlying integral module of the units representation is `Additive Ksepˣ`. -/
theorem unitsModule_obj :
    (unitsModule K Ksep).obj.V = ModuleCat.of ℤ (Additive Ksepˣ) := rfl

/-- The units representation acts by the additive form of the canonical Galois action. -/
theorem unitsModule_rho (σ : Gal(Ksep / K)) :
    (unitsModule K Ksep).obj.ρ σ = ModuleCat.ofHom
      ((MulDistribMulAction.toMonoidHom (A := Ksepˣ) σ).toAdditive.toIntLinearMap) := rfl

/-- Continuous second cohomology with discrete separable-closure units as coefficients. -/
noncomputable abbrev h2Units : Type _ :=
  _root_.continuousCohomology 2
    (DiscreteModuleCat.toTopRep (Gal(Ksep / K)) (unitsModule K Ksep))

/-- The units cohomology carrier is the second homogeneous continuous-cochain cohomology. -/
theorem h2Units_def :
    h2Units K Ksep = _root_.continuousCohomology 2
      (DiscreteModuleCat.toTopRep (Gal(Ksep / K)) (unitsModule K Ksep)) := rfl

/-- Homogenizing a locally constant units cochain gives a continuous map with discrete coefficients. -/
theorem homogeneousTwoCochain_continuous
    (b : LocallyConstant (Gal(Ksep / K) × Gal(Ksep / K)) Ksepˣ) :
    Continuous (fun p : Gal(Ksep / K) × (Gal(Ksep / K) × Gal(Ksep / K)) ↦
      (Additive.ofMul (p.1 • b (p.1⁻¹ * p.2.1, p.2.1⁻¹ * p.2.2)) :
        (DiscreteModuleCat.toTopRep (Gal(Ksep / K)) (unitsModule K Ksep)).V)) := by
  letI : TopologicalSpace Ksepˣ := ⊥
  letI : DiscreteTopology Ksepˣ := ⟨rfl⟩
  letI : ContinuousSMul (Gal(Ksep / K)) Ksepˣ :=
    continuousSMul_iff_stabilizer_isOpen.mpr fun x ↦
      unitsAction_openStabilizer K Ksep (Additive.ofMul x)
  have hc : Continuous (fun p : Gal(Ksep / K) × (Gal(Ksep / K) × Gal(Ksep / K)) ↦
      p.1 • b (p.1⁻¹ * p.2.1, p.2.1⁻¹ * p.2.2)) :=
    continuous_fst.smul (b.continuous.comp
      ((continuous_fst.inv.mul continuous_snd.fst).prodMk
        (continuous_snd.fst.inv.mul continuous_snd.snd)))
  exact ((IsLocallyConstant.iff_continuous _).mpr hc).comp Additive.ofMul |>.continuous

/-- The homogeneous cochain associated to `b` has value
`Additive.ofMul (σ₀ • b (σ₀⁻¹ * σ₁, σ₁⁻¹ * σ₂))`. -/
noncomputable def homogeneousTwoCochain
    (b : LocallyConstant (Gal(Ksep / K) × Gal(Ksep / K)) Ksepˣ) :
    (TopRep.resolutionX
      (DiscreteModuleCat.toTopRep (Gal(Ksep / K)) (unitsModule K Ksep)) 3).V :=
  let cochain : C(Gal(Ksep / K) × (Gal(Ksep / K) × Gal(Ksep / K)),
      (DiscreteModuleCat.toTopRep (Gal(Ksep / K)) (unitsModule K Ksep)).V) :=
    ⟨fun p ↦ Additive.ofMul (p.1 • b (p.1⁻¹ * p.2.1, p.2.1⁻¹ * p.2.2)),
      homogeneousTwoCochain_continuous K Ksep b⟩
  (⟨ContinuousMap.curry, ContinuousMap.continuous_curry⟩ :
    C(C(Gal(Ksep / K) × Gal(Ksep / K),
        (DiscreteModuleCat.toTopRep (Gal(Ksep / K)) (unitsModule K Ksep)).V),
      C(Gal(Ksep / K), C(Gal(Ksep / K),
        (DiscreteModuleCat.toTopRep (Gal(Ksep / K)) (unitsModule K Ksep)).V)))).comp
    cochain.curry

/-- Homogenization of a units cochain is invariant under the diagonal Galois action. -/
theorem homogeneousTwoCochain_invariant
    (b : LocallyConstant (Gal(Ksep / K) × Gal(Ksep / K)) Ksepˣ) :
    homogeneousTwoCochain K Ksep b ∈
      (TopRep.resolutionX
        (DiscreteModuleCat.toTopRep (Gal(Ksep / K)) (unitsModule K Ksep)) 3).ρ.invariants := by
  intro σ
  apply ContinuousMap.ext
  intro σ₀
  apply ContinuousMap.ext
  intro σ₁
  apply ContinuousMap.ext
  intro σ₂
  change Additive.ofMul (σ • ((σ⁻¹ * σ₀) •
      b ((σ⁻¹ * σ₀)⁻¹ * (σ⁻¹ * σ₁), (σ⁻¹ * σ₁)⁻¹ * (σ⁻¹ * σ₂)))) =
    Additive.ofMul (σ₀ • b (σ₀⁻¹ * σ₁, σ₁⁻¹ * σ₂))
  rw [← mul_smul]
  simp [mul_assoc]

/-- The homogeneous cochain of a multiplicative two-cocycle has zero differential. -/
theorem homogeneousTwoCochain_closed
    (b : LocallyConstant (Gal(Ksep / K) × Gal(Ksep / K)) Ksepˣ)
    (hb : groupCohomology.IsMulCocycle₂ b) :
    (((TopRep.homogeneousCochains
      (DiscreteModuleCat.toTopRep (Gal(Ksep / K)) (unitsModule K Ksep))).sc 2).g).hom
        ⟨homogeneousTwoCochain K Ksep b, homogeneousTwoCochain_invariant K Ksep b⟩ = 0 := by
  have h : ∀ j : ℕ, j = 3 →
      ((TopRep.homogeneousCochains
        (DiscreteModuleCat.toTopRep (Gal(Ksep / K)) (unitsModule K Ksep))).d 2 j).hom
          ⟨homogeneousTwoCochain K Ksep b, homogeneousTwoCochain_invariant K Ksep b⟩ = 0 := by
    intro j hj
    subst j
    apply Subtype.ext
    rw [TopRep.homogeneousCochains.d_apply]
    apply ContinuousMap.ext
    intro σ₀
    apply ContinuousMap.ext
    intro σ₁
    apply ContinuousMap.ext
    intro σ₂
    apply ContinuousMap.ext
    intro σ₃
    change Additive.ofMul (σ₁ • b (σ₁⁻¹ * σ₂, σ₂⁻¹ * σ₃)) -
      (Additive.ofMul (σ₀ • b (σ₀⁻¹ * σ₂, σ₂⁻¹ * σ₃)) -
        (Additive.ofMul (σ₀ • b (σ₀⁻¹ * σ₁, σ₁⁻¹ * σ₃)) -
          Additive.ofMul (σ₀ • b (σ₀⁻¹ * σ₁, σ₁⁻¹ * σ₂)))) = 0
    have h := congrArg (fun z : Ksepˣ ↦ Additive.ofMul (σ₀ • z))
      (hb (σ₀⁻¹ * σ₁) (σ₁⁻¹ * σ₂) (σ₂⁻¹ * σ₃))
    simp only [smul_mul', ofMul_mul, ← mul_smul, mul_assoc, mul_inv_cancel_left] at h
    rw [sub_eq_zero, eq_sub_iff_add_eq, ← add_sub_assoc, sub_eq_iff_eq_add]
    exact h.symm
  exact h _ ((ComplexShape.up ℕ).next_eq'
    (show (ComplexShape.up ℕ).Rel 2 3 from rfl))

/-- The continuous cohomology class of an actual locally constant multiplicative two-cocycle. -/
noncomputable def twoCocycleClass
    (b : LocallyConstant (Gal(Ksep / K) × Gal(Ksep / K)) Ksepˣ)
    (hb : groupCohomology.IsMulCocycle₂ b) : h2Units K Ksep :=
  (ContinuousCohomology.π
    (DiscreteModuleCat.toTopRep (Gal(Ksep / K)) (unitsModule K Ksep)) 2)
      ((((TopRep.homogeneousCochains
        (DiscreteModuleCat.toTopRep (Gal(Ksep / K)) (unitsModule K Ksep))).sc 2).isoCyclesOfIsLimit
          (TopModuleCat.isLimitKer _)).hom
            ⟨⟨homogeneousTwoCochain K Ksep b, homogeneousTwoCochain_invariant K Ksep b⟩,
              LinearMap.mem_ker.mpr (homogeneousTwoCochain_closed K Ksep b hb)⟩)

/-- A boundary difference gives equal homology classes in a topological-module short complex. -/
private theorem homologyClass_eq_of_sub_eq_boundary
    {R : Type*} [Ring R] [TopologicalSpace R]
    (S : ShortComplex (TopModuleCat R)) (b c : TopModuleCat.ker S.g)
    (a : S.X₁) (h : S.f.hom a = b.1 - c.1) :
    let e : TopModuleCat.ker S.g ≅ S.cycles :=
      S.isoCyclesOfIsLimit (TopModuleCat.isLimitKer S.g)
    S.homologyπ.hom (e.hom.hom b) = S.homologyπ.hom (e.hom.hom c) := by
  let e : TopModuleCat.ker S.g ≅ S.cycles :=
    S.isoCyclesOfIsLimit (TopModuleCat.isLimitKer S.g)
  let D : S.X₁ ⟶ TopModuleCat.ker S.g := TopModuleCat.ofHom
    (S.f.hom.codRestrict S.g.hom.ker fun x ↦
      LinearMap.mem_ker.mpr (ConcreteCategory.congr_hom S.zero x))
  have hD : D ≫ e.hom = S.toCycles := by
    apply (cancel_mono S.iCycles).mp
    calc
      (D ≫ e.hom) ≫ S.iCycles = D ≫ (e.hom ≫ S.iCycles) := Category.assoc _ _ _
      _ = D ≫ TopModuleCat.kerι S.g := by
        rw [show e.hom ≫ S.iCycles = TopModuleCat.kerι S.g from
          S.isoCyclesOfIsLimit_hom_iCycles (TopModuleCat.isLimitKer S.g)]
      _ = S.f := rfl
      _ = S.toCycles ≫ S.iCycles := S.toCycles_i.symm
  have hboundary : D ≫ e.hom ≫ S.homologyπ = 0 := by
    rw [← Category.assoc, hD, S.toCycles_comp_homologyπ]
  have hdiff : D a = b - c := Subtype.ext h
  have hzero : S.homologyπ.hom (e.hom.hom (b - c)) = 0 := by
    rw [← hdiff]
    exact ConcreteCategory.congr_hom hboundary a
  rw [e.hom.hom.map_sub b c,
    S.homologyπ.hom.map_sub (e.hom.hom b) (e.hom.hom c)] at hzero
  exact sub_eq_zero.mp hzero

/-- Locally constant multiplicative two-cocycles differing by a continuous coboundary
define the same continuous cohomology class. -/
theorem twoCocycleClass_eq_of_coboundary
    (b c : LocallyConstant (Gal(Ksep / K) × Gal(Ksep / K)) Ksepˣ)
    (hb : groupCohomology.IsMulCocycle₂ b) (hc : groupCohomology.IsMulCocycle₂ c)
    (a : LocallyConstant (Gal(Ksep / K)) Ksepˣ)
    (hbc : ∀ σ τ, b (σ, τ) = c (σ, τ) * (σ • a τ / a (σ * τ) * a σ)) :
    twoCocycleClass K Ksep b hb = twoCocycleClass K Ksep c hc := by
  let X := DiscreteModuleCat.toTopRep (Gal(Ksep / K)) (unitsModule K Ksep)
  let C := TopRep.homogeneousCochains X
  have hprev : (ComplexShape.up ℕ).prev 2 = 1 :=
    (ComplexShape.up ℕ).prev_eq' (show (ComplexShape.up ℕ).Rel 1 2 from rfl)
  have hnext : (ComplexShape.up ℕ).next 2 = 3 :=
    (ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel 2 3 from rfl)
  have aux (i j : ℕ) (hi : i = 1) (hj : j = 3)
      (hb' : (C.d 2 j).hom
        ⟨homogeneousTwoCochain K Ksep b, homogeneousTwoCochain_invariant K Ksep b⟩ = 0)
      (hc' : (C.d 2 j).hom
        ⟨homogeneousTwoCochain K Ksep c, homogeneousTwoCochain_invariant K Ksep c⟩ = 0) :
      let S : ShortComplex (TopModuleCat ℤ) :=
        ShortComplex.mk (C.d i 2) (C.d 2 j) (C.d_comp_d i 2 j)
      let e : TopModuleCat.ker S.g ≅ S.cycles :=
        S.isoCyclesOfIsLimit (TopModuleCat.isLimitKer S.g)
      S.homologyπ.hom (e.hom.hom
        ⟨⟨homogeneousTwoCochain K Ksep b, homogeneousTwoCochain_invariant K Ksep b⟩,
          LinearMap.mem_ker.mpr hb'⟩) =
      S.homologyπ.hom (e.hom.hom
        ⟨⟨homogeneousTwoCochain K Ksep c, homogeneousTwoCochain_invariant K Ksep c⟩,
          LinearMap.mem_ker.mpr hc'⟩) := by
    subst i
    subst j
    let S : ShortComplex (TopModuleCat ℤ) :=
      ShortComplex.mk (C.d 1 2) (C.d 2 3) (C.d_comp_d 1 2 3)
    let a₂ : LocallyConstant (Gal(Ksep / K) × Gal(Ksep / K)) Ksepˣ :=
      LocallyConstant.comap ⟨Prod.fst, continuous_fst⟩ a
    have ha : Continuous (fun p : Gal(Ksep / K) × Gal(Ksep / K) ↦
        (Additive.ofMul (p.1 • a (p.1⁻¹ * p.2)) : X.V)) :=
      (homogeneousTwoCochain_continuous K Ksep a₂).comp
        (continuous_fst.prodMk (continuous_snd.prodMk continuous_snd))
    let A : (TopRep.resolutionX X 2).V :=
      (⟨fun p : Gal(Ksep / K) × Gal(Ksep / K) ↦
        Additive.ofMul (p.1 • a (p.1⁻¹ * p.2)), ha⟩ :
        C(Gal(Ksep / K) × Gal(Ksep / K), X.V)).curry
    have hA : A ∈ (TopRep.resolutionX X 2).ρ.invariants := by
      intro σ
      apply ContinuousMap.ext
      intro σ₀
      apply ContinuousMap.ext
      intro σ₁
      change Additive.ofMul (σ • ((σ⁻¹ * σ₀) •
        a ((σ⁻¹ * σ₀)⁻¹ * (σ⁻¹ * σ₁)))) = Additive.ofMul (σ₀ • a (σ₀⁻¹ * σ₁))
      rw [← mul_smul]
      simp [mul_assoc]
    let aC : S.X₁ := ⟨A, hA⟩
    let zb : TopModuleCat.ker S.g :=
      ⟨⟨homogeneousTwoCochain K Ksep b, homogeneousTwoCochain_invariant K Ksep b⟩,
        LinearMap.mem_ker.mpr hb'⟩
    let zc : TopModuleCat.ker S.g :=
      ⟨⟨homogeneousTwoCochain K Ksep c, homogeneousTwoCochain_invariant K Ksep c⟩,
        LinearMap.mem_ker.mpr hc'⟩
    apply homologyClass_eq_of_sub_eq_boundary S zb zc aC
    apply Subtype.ext
    change (((TopRep.homogeneousCochains X).d 1 (1 + 1)).hom aC).1 = _
    rw [TopRep.homogeneousCochains.d_apply]
    apply ContinuousMap.ext
    intro σ₀
    apply ContinuousMap.ext
    intro σ₁
    apply ContinuousMap.ext
    intro σ₂
    change Additive.ofMul (σ₁ • a (σ₁⁻¹ * σ₂)) -
      (Additive.ofMul (σ₀ • a (σ₀⁻¹ * σ₂)) - Additive.ofMul (σ₀ • a (σ₀⁻¹ * σ₁))) =
      Additive.ofMul (σ₀ • b (σ₀⁻¹ * σ₁, σ₁⁻¹ * σ₂)) -
        Additive.ofMul (σ₀ • c (σ₀⁻¹ * σ₁, σ₁⁻¹ * σ₂))
    have h := congrArg (fun z : Ksepˣ ↦ Additive.ofMul (σ₀ • z))
      (hbc (σ₀⁻¹ * σ₁) (σ₁⁻¹ * σ₂))
    simp only [smul_mul', smul_div', ofMul_mul, ofMul_div,
      ← mul_smul, mul_assoc, mul_inv_cancel_left] at h
    rw [h, add_sub_cancel_left]
    abel
  exact aux _ _ hprev hnext (homogeneousTwoCochain_closed K Ksep b hb)
    (homogeneousTwoCochain_closed K Ksep c hc)

end GaloisCohomology

end
