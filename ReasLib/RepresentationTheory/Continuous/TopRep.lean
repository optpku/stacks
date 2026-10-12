/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.RingTheory.AdicCompletion.Basic

@[expose] public section

open CategoryTheory
open ContRepresentation
open scoped ContRepresentation

noncomputable section

universe u

namespace ContinuousModule

/-- The continuous action maps of a profinite module satisfy the identity law. -/
theorem profiniteTopRep_map_one (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (M : Type u) [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [CompactSpace M] [T2Space M]
    [TotallyDisconnectedSpace M] [DistribMulAction G M] [ContinuousSMul G M]
    (x : M) : (DistribSMul.toAddMonoidHom M 1).toIntLinearMap x = x := sorry

/-- The continuous action maps of a profinite module satisfy multiplication. -/
theorem profiniteTopRep_map_mul (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (M : Type u) [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [CompactSpace M] [T2Space M]
    [TotallyDisconnectedSpace M] [DistribMulAction G M] [ContinuousSMul G M]
    (g h : G) (x : M) :
    (DistribSMul.toAddMonoidHom M (g * h)).toIntLinearMap x =
      (DistribSMul.toAddMonoidHom M g).toIntLinearMap
        ((DistribSMul.toAddMonoidHom M h).toIntLinearMap x) := sorry

/-- The `I`-adic topology makes a module a topological additive group. -/
theorem adicModule_isTopologicalAddGroup {Λ : Type u} [CommRing Λ] (I : Ideal Λ)
    (M : Type u) [AddCommGroup M] [Module Λ M] :
    @IsTopologicalAddGroup M (Ideal.adicModuleTopology I M) _ := sorry

/-- Integer scalars act continuously in the `I`-adic topology. -/
theorem adicModule_continuousSMul_int {Λ : Type u} [CommRing Λ] (I : Ideal Λ)
    (M : Type u) [AddCommGroup M] [Module Λ M] :
    @ContinuousSMul ℤ M _ _ (Ideal.adicModuleTopology I M) := sorry

/-- The topological representation associated to a profinite continuous module. -/
public def profiniteTopRep (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (M : Type u) [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [CompactSpace M] [T2Space M]
    [TotallyDisconnectedSpace M] [DistribMulAction G M] [ContinuousSMul G M] :
    TopRep ℤ G :=
  TopRep.of
    { toMonoidHom :=
        { toFun := fun g ↦
          { toLinearMap := (DistribSMul.toAddMonoidHom M g).toIntLinearMap
            cont := continuous_const_smul g }
          map_one' := by
            apply ContinuousLinearMap.ext
            intro x
            simpa using profiniteTopRep_map_one G M x
          map_mul' := by
            intro g h
            apply ContinuousLinearMap.ext
            intro x
            simpa using profiniteTopRep_map_mul G M g h x } }

/-- The action of a group element is continuous for the adic topology. -/
theorem adicAction_continuous (G : Type u) [Group G] [TopologicalSpace G]
    {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u) [AddCommGroup M]
    [Module Λ M] [DistribMulAction G M]
    [hcont : @ContinuousSMul G M _ _ (Ideal.adicModuleTopology I M)] (g : G) :
    @Continuous M M (Ideal.adicModuleTopology I M) (Ideal.adicModuleTopology I M)
      (DistribSMul.toAddMonoidHom M g) := sorry

/-- The continuous integral-linear action map of a group element on an adic module. -/
public def adicActionCLM (G : Type u) [Group G] [TopologicalSpace G]
    {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u)
    [AddCommGroup M] [Module Λ M] [DistribMulAction G M]
    [hcont : @ContinuousSMul G M _ _ (Ideal.adicModuleTopology I M)] (g : G) :
    @ContinuousLinearMap ℤ ℤ _ _ (RingHom.id ℤ) M (Ideal.adicModuleTopology I M) _ M
      (Ideal.adicModuleTopology I M) _ _ _ :=
  @ContinuousLinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ) M (Ideal.adicModuleTopology I M) _ M
    (Ideal.adicModuleTopology I M) _ _ _
    (DistribSMul.toAddMonoidHom M g).toIntLinearMap (adicAction_continuous G I M g)

/-- The adic action map preserves the identity element of the group. -/
theorem adicContRepresentation_map_one (G : Type u) [Group G] [TopologicalSpace G]
    {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u) [AddCommGroup M]
    [Module Λ M] [DistribMulAction G M]
    [hcont : @ContinuousSMul G M _ _ (Ideal.adicModuleTopology I M)] (x : M) :
    adicActionCLM G I M 1 x = x := sorry

/-- The adic action map preserves multiplication in the group. -/
theorem adicContRepresentation_map_mul (G : Type u) [Group G] [TopologicalSpace G]
    {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u) [AddCommGroup M]
    [Module Λ M] [DistribMulAction G M]
    [hcont : @ContinuousSMul G M _ _ (Ideal.adicModuleTopology I M)] (g h : G) (x : M) :
    adicActionCLM G I M (g * h) x =
      adicActionCLM G I M g (adicActionCLM G I M h x) := sorry

/-- The continuous integral representation of a group on an adic module. -/
public def adicContRepresentation (G : Type u) [Group G] [TopologicalSpace G]
    {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u)
    [AddCommGroup M] [Module Λ M] [DistribMulAction G M]
    [hcont : @ContinuousSMul G M _ _ (Ideal.adicModuleTopology I M)] :
    @ContRepresentation ℤ G M _ _ _ (Ideal.adicModuleTopology I M)
      (adicModule_isTopologicalAddGroup I M) _ :=
  -- Local instance justification (defeq pin): the explicit adic topology is needed by extensionality.
  letI : TopologicalSpace M := Ideal.adicModuleTopology I M
  @ContRepresentation.ofMonoidHom ℤ G M _ _ _ (Ideal.adicModuleTopology I M)
    (adicModule_isTopologicalAddGroup I M) _
    { toFun := fun g ↦ adicActionCLM G I M g
      map_one' := by
        apply ContinuousLinearMap.ext
        intro x
        exact adicContRepresentation_map_one G I M x
      map_mul' := by
        intro g h
        apply ContinuousLinearMap.ext
        intro x
        exact adicContRepresentation_map_mul G I M g h x }

/-- The topological representation of an adically complete module. -/
public def adicTopRep (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u)
    [AddCommGroup M] [Module Λ M] [IsAdicComplete I M]
    [DistribMulAction G M]
    [hcont : @ContinuousSMul G M _ _ (Ideal.adicModuleTopology I M)] :
    TopRep ℤ G :=
  @TopRep.of ℤ G M _ _ _ _ _ (Ideal.adicModuleTopology I M)
    (adicModule_isTopologicalAddGroup I M) (adicModule_continuousSMul_int I M)
    (adicContRepresentation G I M)

/-- The carrier of `profiniteTopRep` is the original coefficient module. -/
theorem profiniteTopRep_V (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (M : Type u) [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [CompactSpace M] [T2Space M]
    [TotallyDisconnectedSpace M] [DistribMulAction G M] [ContinuousSMul G M] :
    (profiniteTopRep G M).V = M := sorry

/-- The carrier of `adicTopRep` is the original coefficient module. -/
theorem adicTopRep_V (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u)
    [AddCommGroup M] [Module Λ M] [IsAdicComplete I M] [DistribMulAction G M]
    [hcont : @ContinuousSMul G M _ _ (Ideal.adicModuleTopology I M)] :
    (adicTopRep G I M).V = M := sorry

/-- Scalar multiplication is continuous for the adic topology. -/
theorem adicScalar_continuous (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u)
    [AddCommGroup M] [Module Λ M] [IsAdicComplete I M] [DistribMulAction G M]
    [SMulCommClass G Λ M]
    [hcont : @ContinuousSMul G M _ _ (Ideal.adicModuleTopology I M)] (r : Λ) :
    @Continuous M M (Ideal.adicModuleTopology I M) (Ideal.adicModuleTopology I M)
      (DistribSMul.toAddMonoidHom M r) := sorry

/-- Scalar multiplication intertwines the adic group representation. -/
theorem adicScalar_isIntertwining (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u)
    [AddCommGroup M] [Module Λ M] [IsAdicComplete I M] [DistribMulAction G M]
    [SMulCommClass G Λ M]
    [hcont : @ContinuousSMul G M _ _ (Ideal.adicModuleTopology I M)] (r : Λ) :
    ∀ g : G, ∀ x : M, r • g • x = g • r • x := sorry

/-- Scalar multiplication on an adic coefficient representation. -/
public def adicTopRep_smul (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (M : Type u)
    [AddCommGroup M] [Module Λ M] [IsAdicComplete I M] [DistribMulAction G M]
    [SMulCommClass G Λ M]
    [hcont : @ContinuousSMul G M _ _ (Ideal.adicModuleTopology I M)] (r : Λ) :
    adicTopRep G I M ⟶ adicTopRep G I M :=
  ConcreteCategory.ofHom
    ({ toLinearMap := (DistribSMul.toAddMonoidHom M r).toIntLinearMap
       cont := adicScalar_continuous G I M r
       isIntertwining' := by
         intro g
         apply ContinuousLinearMap.ext
         intro x
         exact adicScalar_isIntertwining G I M r g x } :
      (adicTopRep G I M).ρ →ⁱL (adicTopRep G I M).ρ)

end ContinuousModule

end
