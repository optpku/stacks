/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
        (1 : End (ModuleCat.of ℤ (Additive Ksepˣ))) := sorry

/-- Composition of Galois automorphisms induces composition of integral linear maps on units. -/
theorem unitsAction_map_mul (σ τ : Gal(Ksep / K)) :
    ModuleCat.ofHom
      ((MulDistribMulAction.toMonoidHom (A := Ksepˣ) (σ * τ)).toAdditive.toIntLinearMap) =
      ModuleCat.ofHom
        ((MulDistribMulAction.toMonoidHom (A := Ksepˣ) τ).toAdditive.toIntLinearMap) ≫
      ModuleCat.ofHom
        ((MulDistribMulAction.toMonoidHom (A := Ksepˣ) σ).toAdditive.toIntLinearMap) := sorry

/-- The integral linear action of the absolute Galois group on separable-closure units. -/
noncomputable def unitsAction : Gal(Ksep / K) →* End (ModuleCat.of ℤ (Additive Ksepˣ)) where
  toFun σ := ModuleCat.ofHom
    ((MulDistribMulAction.toMonoidHom (A := Ksepˣ) σ).toAdditive.toIntLinearMap)
  map_one' := unitsAction_map_one K Ksep
  map_mul' := unitsAction_map_mul K Ksep

/-- Every separable-closure unit has open stabilizer for the canonical Galois action. -/
theorem unitsAction_openStabilizer :
    openStabilizer ℤ (Gal(Ksep / K))
      { V := ModuleCat.of ℤ (Additive Ksepˣ), ρ := unitsAction K Ksep } := sorry

/-- The discrete integral Galois module of separable-closure units, viewed additively. -/
noncomputable def unitsModule : DiscreteModuleCat ℤ (Gal(Ksep / K)) :=
  ⟨{ V := ModuleCat.of ℤ (Additive Ksepˣ), ρ := unitsAction K Ksep },
    unitsAction_openStabilizer K Ksep⟩

/-- The underlying integral module of the units representation is `Additive Ksepˣ`. -/
theorem unitsModule_obj :
    (unitsModule K Ksep).obj.V = ModuleCat.of ℤ (Additive Ksepˣ) := sorry

/-- The units representation acts by the additive form of the canonical Galois action. -/
theorem unitsModule_rho (σ : Gal(Ksep / K)) :
    (unitsModule K Ksep).obj.ρ σ = ModuleCat.ofHom
      ((MulDistribMulAction.toMonoidHom (A := Ksepˣ) σ).toAdditive.toIntLinearMap) := sorry

/-- Continuous second cohomology with discrete separable-closure units as coefficients. -/
noncomputable abbrev h2Units : Type _ :=
  _root_.continuousCohomology 2
    (DiscreteModuleCat.toTopRep (Gal(Ksep / K)) (unitsModule K Ksep))

/-- The units cohomology carrier is the second homogeneous continuous-cochain cohomology. -/
theorem h2Units_def :
    h2Units K Ksep = _root_.continuousCohomology 2
      (DiscreteModuleCat.toTopRep (Gal(Ksep / K)) (unitsModule K Ksep)) := sorry

/-- Homogenizing a locally constant units cochain gives a continuous map with discrete coefficients. -/
theorem homogeneousTwoCochain_continuous
    (b : LocallyConstant (Gal(Ksep / K) × Gal(Ksep / K)) Ksepˣ) :
    Continuous (fun p : Gal(Ksep / K) × (Gal(Ksep / K) × Gal(Ksep / K)) ↦
      (Additive.ofMul (p.1 • b (p.1⁻¹ * p.2.1, p.2.1⁻¹ * p.2.2)) :
        (DiscreteModuleCat.toTopRep (Gal(Ksep / K)) (unitsModule K Ksep)).V)) := sorry

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
        (DiscreteModuleCat.toTopRep (Gal(Ksep / K)) (unitsModule K Ksep)) 3).ρ.invariants := sorry

/-- The homogeneous cochain of a multiplicative two-cocycle has zero differential. -/
theorem homogeneousTwoCochain_closed
    (b : LocallyConstant (Gal(Ksep / K) × Gal(Ksep / K)) Ksepˣ)
    (hb : groupCohomology.IsMulCocycle₂ b) :
    (((TopRep.homogeneousCochains
      (DiscreteModuleCat.toTopRep (Gal(Ksep / K)) (unitsModule K Ksep))).sc 2).g).hom
        ⟨homogeneousTwoCochain K Ksep b, homogeneousTwoCochain_invariant K Ksep b⟩ = 0 := sorry

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

/-- Locally constant multiplicative two-cocycles differing by a continuous coboundary
define the same continuous cohomology class. -/
theorem twoCocycleClass_eq_of_coboundary
    (b c : LocallyConstant (Gal(Ksep / K) × Gal(Ksep / K)) Ksepˣ)
    (hb : groupCohomology.IsMulCocycle₂ b) (hc : groupCohomology.IsMulCocycle₂ c)
    (a : LocallyConstant (Gal(Ksep / K)) Ksepˣ)
    (hbc : ∀ σ τ, b (σ, τ) = c (σ, τ) * (σ • a τ / a (σ * τ) * a σ)) :
    twoCocycleClass K Ksep b hb = twoCocycleClass K Ksep c hc := sorry

end GaloisCohomology

end
