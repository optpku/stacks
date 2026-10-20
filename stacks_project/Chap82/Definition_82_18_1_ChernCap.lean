/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.ClosureIntegral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.GenericSection
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InvertiblePullback
public import stacks_project.Chap67.Lemma_67_4_9
public import stacks_project.Chap82.Definition_82_15_1_Chow
public import stacks_project.Chap82.Definition_82_15_1_ClosedPushforward
public import stacks_project.Chap82.Definition_82_17_1_Cycle

/-! # The original EQK/EQQ target with the concrete closed-image pullback

This is the source-facing ChernCap component, with the same good-space
parameters and the exact point-closure target. Its line module and section
use the explicit geometric/tensor pullback and the concrete generic
restriction. No new affine, decency, or quasi-separated hypothesis is added.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace.Hom
open Function Set Topology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom



variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable (L : X.Modules.{u}) [isInvertibleObject L]

/-- The exact source façade, retaining the original point-closure carrier. -/
abbrev closureSpace (x : Points X) := PointClosure.space x

abbrev closureI (x : Points X) : closureSpace x ⟶ X := PointClosure.ι x

/-- The actual original-u module pullback on the closed image. -/
def line (L : X.Modules.{u}) (x : Points X) : (closureSpace x).Modules.{u} :=
  (Modules.pullback (closureI x)).obj L

/-- Tensor-invertibility of the specified module. This is a law of the
explicit pullback; it does not select a trivialization. -/
theorem line_invertible (L : X.Modules.{u}) [isInvertibleObject L] (x : Points X) : isInvertibleObject (line L x) :=
  Modules.isInvertibleObject_pullback (PointClosure.ι x) L

/-- A closed subspace of the source of a good morphism is quasi-separated. -/
theorem closure_quasiSeparatedSpace (f : X ⟶ B) [QuasiSeparated f]
    (x : Points X) : AlgebraicSpace.IsQuasiSeparated (PointClosure.space x) := by
  -- Local instance justification (proof-local temporary data): The supplied quasi-separated structure morphism f gives quasi-separatedness of X, needed for the actual reduced point closure.
  letI := IsQuasiSeparated.of_quasiSeparated f
  exact PointClosure.quasiSeparated x

/-- Integrality is used only in the original good-space range and its
decency field is supplied by the concrete residual-field construction. -/
theorem closure_integral (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (x : Points X) : AlgebraicSpace.IsIntegral (PointClosure.space x) := by
  -- Local instance justification (proof-local temporary data): The supplied quasi-separated structure morphism f gives quasi-separatedness of X, needed for the actual reduced point closure.
  letI := IsQuasiSeparated.of_quasiSeparated f
  exact PointClosure.integral x

/-- The concrete generic section on the actual line module. -/
def firstChernMeromorphicSection (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (L : X.Modules.{u}) [isInvertibleObject L] (x : Points X) :
    meromorphicSections (closureSpace x) (line L x) := by
  -- Local instance justification (proof-local temporary data): Use integrality of the actual reduced closure of x to evaluate its generic line fibre and form its divisor.
  letI := closure_integral f x
  -- Local instance justification (proof-local temporary data): Use quasi-separatedness of the actual reduced point closure for the generic-fibre meromorphic restriction theorem.
  letI := closure_quasiSeparatedSpace f x
  -- Local instance justification (proof-local temporary data): The line is the genuine pullback of L to the point closure; use its inherited invertibility for the generic nonzero section.
  letI := line_invertible L x
  exact MeromorphicConstruction.GenericSection.sectionValue (closureSpace x)
    (PointClosure.generic_mem x) (line L x)

theorem firstChernMeromorphicSection_isRegular (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (L : X.Modules.{u}) [isInvertibleObject L] (x : Points X) :
    IsRegularMeromorphicSection (closureSpace x) (line L x) (firstChernMeromorphicSection f L x) := by
  -- Local instance justification (proof-local temporary data): Use integrality of the actual reduced closure of x to evaluate its generic line fibre and form its divisor.
  letI := closure_integral f x
  -- Local instance justification (proof-local temporary data): Use quasi-separatedness of the actual reduced point closure for the generic-fibre meromorphic restriction theorem.
  letI := closure_quasiSeparatedSpace f x
  -- Local instance justification (proof-local temporary data): The line is the genuine pullback of L to the point closure; use its inherited invertibility for the generic nonzero section.
  letI := line_invertible L x
  exact MeromorphicConstruction.GenericSection.sectionValue_regular (closureSpace x)
    (PointClosure.generic_mem x) (line L x)

theorem closure_quasiSeparated (x : Points X) :
    QuasiSeparated (closureI x ≫ f) := by
  sorry

theorem closure_locallyOfFiniteType (x : Points X) :
    LocallyOfFiniteType (closureI x ≫ f) := by
  sorry

/-- The source-facing divisor uses the concrete line and section. -/
noncomputable def restrictedDivisor (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (L : X.Modules.{u}) [isInvertibleObject L] (x : Points X) :
    Function.locallyFinsupp (Points (closureSpace x)) ℤ := by
  -- Local instance justification (proof-local temporary data): Use integrality of the actual reduced closure of x to evaluate its generic line fibre and form its divisor.
  letI := closure_integral f x
  exact @Hom.meromorphicSectionDivisorCycle S B (closureSpace x) inferInstance inferInstance
    (closureI x ≫ f) (closure_quasiSeparated f x) (closure_locallyOfFiniteType f x)
    δ inferInstance inferInstance (line L x) (line_invertible L x) (firstChernMeromorphicSection f L x)
    (firstChernMeromorphicSection_isRegular f L x)

theorem restrictedDivisor_mem (k : ℤ) (x : Points X)
    (hx : (relativeDimensionFunction f) δ x = k + 1) :
    restrictedDivisor f δ L x ∈ Hom.cycleGroup (closureI x ≫ f) δ k := by
  sorry

/-- The final concrete generator for first Chern cap. -/
noncomputable def firstChernGeneratorCycle (k : ℤ) (x : Points X)
    (hx : Hom.relativeDimensionFunction f δ x = k + 1) :
    Function.locallyFinsupp (Points X) ℤ := by
  let _ := hx
  -- Local instance justification (proof-local temporary data): Use the closed-immersion law of the specified point-closure inclusion when applying its cycle pushforward.
  letI : AlgebraicSpace.IsClosedImmersion (closureI x) :=
    PointClosure.instIsClosedImmersion_ι x
  exact closedImmersionPushforwardCycle (ClosedSubspace.ofι (closureI x))
    (restrictedDivisor f δ L x)

theorem firstChernGeneratorCycle_mem (k : ℤ) (x : Points X)
    (hx : (relativeDimensionFunction f) δ x = k + 1) :
    firstChernGeneratorCycle f δ L k x hx ∈ Hom.cycleGroup f δ k := by
  sorry

/-- Locally finite input cycles give locally finite families of the actual
point-closure divisor cycles, in the original dimension-function range. -/
theorem firstChernGeneratorTermsLocallyFinite (k : ℤ)
    (α : Function.locallyFinsupp (Points X) ℤ) :
    LocallyFinite fun x : Points X ↦
      (if hx : relativeDimensionFunction f δ x = k + 1 then
        α x • firstChernGeneratorCycle f δ L k x hx else 0).support := by
  sorry

/-- Full cycle construction, using locally finite sums of the actual generators. -/
def firstChernCycle (k : ℤ) (α : Function.locallyFinsupp (Points X) ℤ) :
    Function.locallyFinsupp (Points X) ℤ :=
  AlgebraicCycle.locallyFiniteSum
    (fun x : Points X ↦ if hx : relativeDimensionFunction f δ x = k + 1 then
      α x • firstChernGeneratorCycle f δ L k x hx else 0)
    (firstChernGeneratorTermsLocallyFinite f δ L k α)

theorem firstChernCycle_mem (k : ℤ) (α : cycleGroup f δ (k + 1)) :
    firstChernCycle f δ L k (α : Function.locallyFinsupp (Points X) ℤ) ∈ cycleGroup f δ k := by
  sorry

/-- Concrete final Chow-group value, retaining the original grading. -/
def firstChernCapValue (k : ℤ) (α : cycleGroup f δ (k + 1)) : chowGroup f δ k :=
  chowMk f δ k ⟨firstChernCycle f δ L k α, firstChernCycle_mem f δ L k α⟩

theorem firstChernClassCap_zero (k : ℤ) : firstChernCapValue f δ L k 0 = 0 := by sorry

theorem firstChernClassCap_add (k : ℤ) (α β : cycleGroup f δ (k + 1)) :
    firstChernCapValue f δ L k (α + β) = firstChernCapValue f δ L k α + firstChernCapValue f δ L k β := by sorry

/-- The full original-target map Z_(k+1)(X) → CH_k(X), with no extra
source hypothesis or independently chosen section. -/
def firstChernClassCap (k : ℤ) : cycleGroup f δ (k + 1) →+ chowGroup f δ k where
  toFun := firstChernCapValue f δ L k
  map_zero' := firstChernClassCap_zero f δ L k
  map_add' := firstChernClassCap_add f δ L k

theorem firstChernClassCap_apply (k : ℤ) (α : cycleGroup f δ (k + 1)) :
    firstChernClassCap f δ L k α =
      chowMk f δ k ⟨firstChernCycle f δ L k α, firstChernCycle_mem f δ L k α⟩ := rfl

/-- The divisor cycle of a regular meromorphic section of a pullback invertible
module, as a cycle on the source of `i`. -/
noncomputable def firstChernRestrictedDivisorCycle (Y : AlgebraicSpace S)
    (i : Y ⟶ X) [IsIntegral Y] [QuasiSeparated (i ≫ f)] [LocallyOfFiniteType (i ≫ f)]
    (s : meromorphicSections Y ((Modules.pullback i).obj L))
    (hs : IsRegularMeromorphicSection Y ((Modules.pullback i).obj L) s) :
    Function.locallyFinsupp (Points Y) ℤ :=
  @meromorphicSectionDivisorCycle S B Y inferInstance inferInstance (i ≫ f)
    inferInstance inferInstance δ inferInstance inferInstance
    ((Modules.pullback i).obj L)
    (Modules.isInvertibleObject_pullback i L) s hs

/-- The restricted divisor cycle of a regular meromorphic section on an integral
space of relative dimension `k + 1` is a `k`-cycle. -/
theorem firstChernRestrictedDivisorCycle_mem (k : ℤ) (Y : AlgebraicSpace S)
    (i : Y ⟶ X) [IsIntegral Y] [QuasiSeparated (i ≫ f)] [LocallyOfFiniteType (i ≫ f)]
    (hk : deltaDimension (i ≫ f) δ (univIrreducibleClosed Y) = k + 1)
    (s : meromorphicSections Y ((Modules.pullback i).obj L))
    (hs : IsRegularMeromorphicSection Y ((Modules.pullback i).obj L) s) :
    firstChernRestrictedDivisorCycle f δ L Y i s hs ∈ cycleGroup (i ≫ f) δ k :=
  sorry

/-- Divisor cycle on the concrete closure with explicitly scoped integrality. -/
def firstChernPointClosureDivisorCycle (x : Points X)
    (s : meromorphicSections (PointClosure.space x) ((Modules.pullback (PointClosure.ι x)).obj L))
    (hs : IsRegularMeromorphicSection (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L) s) :
    Function.locallyFinsupp (Points (PointClosure.space x)) ℤ := by
  -- Local instance justification (proof-local temporary data): Use integrality of the actual reduced closure of x to evaluate its generic line fibre and form its divisor.
  letI := closure_integral f x
  -- Local instance justification (proof-local temporary data): The composite of the actual point-closure inclusion with f is quasi-separated, as required by its relative divisor cycle.
  letI := closure_quasiSeparated f x
  -- Local instance justification (proof-local temporary data): The same point-closure structure morphism is locally of finite type, giving the existing relative divisor-cycle scope.
  letI := closure_locallyOfFiniteType f x
  exact firstChernRestrictedDivisorCycle f δ L (PointClosure.space x) (PointClosure.ι x) s hs

/-- The singleton cycle `[W]` of a point of relative dimension `k + 1`. -/
theorem firstChernSingleton_mem (k : ℤ) (x : Points X)
    (hx : (relativeDimensionFunction f) δ x = k + 1) :
    (@Function.locallyFinsuppWithin.single (Points X) _ ℤ (Classical.decEq _) _
        x 1) ∈ (cycleGroup f) δ (k + 1) :=
  sorry

/-- Pushforward of a restricted divisor cycle from the reduced closure of a
degree-`k + 1` point is a `k`-cycle. -/
theorem firstChernClosedSubspacePushforward_mem (k : ℤ) (x : Points X)
    (hx : (relativeDimensionFunction f) δ x = k + 1)
    (s : meromorphicSections (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L))
    (hs : IsRegularMeromorphicSection (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L) s) :
    closedImmersionPushforwardCycle (ClosedSubspace.ofι (PointClosure.ι x))
        (firstChernPointClosureDivisorCycle f δ L x s hs) ∈
      (cycleGroup f) δ k :=
  sorry

/-- On the reduced integral closed subspace `i : W → X` of a point of
relative dimension `k + 1`, `c1(L) ∩ [W]` is the Chow class of
`i_* div_{i^* L}(s)` for any regular meromorphic section of `i^* L`. -/
theorem firstChernClassCap_closedSubspace (k : ℤ) (x : Points X)
    (hx : (relativeDimensionFunction f) δ x = k + 1)
    (s : meromorphicSections (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L))
    (hs : IsRegularMeromorphicSection (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L) s) :
    firstChernClassCap f δ L k
        ⟨@Function.locallyFinsuppWithin.single (Points X) _ ℤ
            (Classical.decEq _) _ x 1,
          firstChernSingleton_mem f δ k x hx⟩ =
      (chowMk f) δ k
        ⟨closedImmersionPushforwardCycle (ClosedSubspace.ofι (PointClosure.ι x))
            (firstChernPointClosureDivisorCycle f δ L x s hs),
          firstChernClosedSubspacePushforward_mem f δ L k x hx s hs⟩ :=
  sorry

/-- The Chow class of `i_* div_{i^* L}(s)` on the reduced closure of a
degree-`k + 1` point is independent of the choice of regular meromorphic
section of `i^* L`. -/
theorem firstChernClassCap_eq_of_meromorphicSection (k : ℤ) (x : Points X)
    (hx : (relativeDimensionFunction f) δ x = k + 1)
    (s : meromorphicSections (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L))
    (hs : IsRegularMeromorphicSection (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L) s)
    (t : meromorphicSections (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L))
    (ht : IsRegularMeromorphicSection (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L) t) :
    (chowMk f) δ k
        ⟨closedImmersionPushforwardCycle (ClosedSubspace.ofι (PointClosure.ι x))
            (firstChernPointClosureDivisorCycle f δ L x s hs),
          firstChernClosedSubspacePushforward_mem f δ L k x hx s hs⟩ =
      (chowMk f) δ k
        ⟨closedImmersionPushforwardCycle (ClosedSubspace.ofι (PointClosure.ι x))
            (firstChernPointClosureDivisorCycle f δ L x t ht),
          firstChernClosedSubspacePushforward_mem f δ L k x hx t ht⟩ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
