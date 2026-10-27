/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.ClosureIntegral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.GenericSection
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.Quotient
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InvertiblePullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Transfer
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.Quotient
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.ClosedPushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.WeilDivisor

/-!
# First Chern intersection from point-closure divisors

For a quasi-separated, locally finite type morphism of algebraic spaces to a
universally catenary, quasi-separated base equipped with a dimension function,
intersection with an invertible module sends cycles of degree `k + 1` to Chow
classes of degree `k`.

On the reduced integral closure of a point, pull back the invertible module,
take the divisor of a regular meromorphic section, and push this divisor cycle
forward along the closure inclusion. Coefficient-weighted locally finite sums
of these generators define the operation on general cycles; passing to Chow
classes gives an additive map independent of the meromorphic sections.

This construction uses the cycle and Chow theories of algebraic spaces.
Extending it to more general ringed sites requires corresponding cycle, divisor,
pushforward, and rational-equivalence theories.
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

/-- A closed subspace of the source of a good morphism is quasi-separated. -/
private theorem closure_quasiSeparatedSpace (f : X ⟶ B) [QuasiSeparated f]
    (x : Points X) : AlgebraicSpace.IsQuasiSeparated (PointClosure.space x) := by
  -- Local instance justification (proof-local temporary data): The supplied quasi-separated structure morphism f gives quasi-separatedness of X, needed for the actual reduced point closure.
  letI := IsQuasiSeparated.of_quasiSeparated f
  exact PointClosure.quasiSeparated x

/-- The reduced closure of a point of a good algebraic space is integral. -/
private theorem closure_integral (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (x : Points X) : AlgebraicSpace.IsIntegral (PointClosure.space x) := by
  -- Local instance justification (proof-local temporary data): The supplied quasi-separated structure morphism f gives quasi-separatedness of X, needed for the actual reduced point closure.
  letI := IsQuasiSeparated.of_quasiSeparated f
  exact PointClosure.integral x

/-- A regular meromorphic section of the pullback of `L` to the reduced integral
closure of `x`, obtained from a nonzero section of its generic fibre. -/
def firstChernMeromorphicSection (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (L : X.Modules.{u}) [isInvertibleObject L] (x : Points X) :
    meromorphicSections (PointClosure.space x) ((Modules.pullback (PointClosure.ι x)).obj L) := by
  -- Local instance justification (proof-local temporary data): Use integrality of the actual reduced closure of x to evaluate its generic line fibre and form its divisor.
  letI : AlgebraicSpace.IsIntegral (PointClosure.space x) := by exact closure_integral f x
  -- Local instance justification (proof-local temporary data): Use quasi-separatedness of the actual reduced point closure for the generic-fibre meromorphic restriction theorem.
  letI : AlgebraicSpace.IsQuasiSeparated (PointClosure.space x) := by
    exact closure_quasiSeparatedSpace f x
  -- Local instance justification (proof-local temporary data): The line is the genuine pullback of L to the point closure; use its inherited invertibility for the generic nonzero section.
  letI := Modules.isInvertibleObject_pullback (PointClosure.ι x) L
  exact MeromorphicConstruction.GenericSection.sectionValue (PointClosure.space x)
    (PointClosure.generic_mem x) ((Modules.pullback (PointClosure.ι x)).obj L)

/-- The generic meromorphic section of the pullback invertible module is regular. -/
theorem firstChernMeromorphicSection_isRegular (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (L : X.Modules.{u}) [isInvertibleObject L] (x : Points X) :
    IsRegularMeromorphicSection (PointClosure.space x) ((Modules.pullback (PointClosure.ι x)).obj L) (firstChernMeromorphicSection f L x) := by
  -- Local instance justification (proof-local temporary data): Use integrality of the actual reduced closure of x to evaluate its generic line fibre and form its divisor.
  letI : AlgebraicSpace.IsIntegral (PointClosure.space x) := by exact closure_integral f x
  -- Local instance justification (proof-local temporary data): Use quasi-separatedness of the actual reduced point closure for the generic-fibre meromorphic restriction theorem.
  letI : AlgebraicSpace.IsQuasiSeparated (PointClosure.space x) := by
    exact closure_quasiSeparatedSpace f x
  -- Local instance justification (proof-local temporary data): The line is the genuine pullback of L to the point closure; use its inherited invertibility for the generic nonzero section.
  letI := Modules.isInvertibleObject_pullback (PointClosure.ι x) L
  exact MeromorphicConstruction.GenericSection.sectionValue_regular (PointClosure.space x)
    (PointClosure.generic_mem x) ((Modules.pullback (PointClosure.ι x)).obj L)

/-- The structure morphism of a point closure is quasi-separated. -/
theorem closure_quasiSeparated (x : Points X) :
    QuasiSeparated (PointClosure.ι x ≫ f) := sorry

/-- The structure morphism of a point closure is locally of finite type. -/
theorem closure_locallyOfFiniteType (x : Points X) :
    LocallyOfFiniteType (PointClosure.ι x ≫ f) := sorry

/-- The divisor of the generic meromorphic section on a point closure. -/
private noncomputable def restrictedDivisor (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (L : X.Modules.{u}) [isInvertibleObject L] (x : Points X) :
    Function.locallyFinsupp (Points (PointClosure.space x)) ℤ := by
  -- Local instance justification (proof-local temporary data): Use integrality of the actual reduced closure of x to evaluate its generic line fibre and form its divisor.
  letI : AlgebraicSpace.IsIntegral (PointClosure.space x) := by exact closure_integral f x
  exact @Hom.meromorphicSectionDivisorCycle S B (PointClosure.space x) inferInstance inferInstance
    (PointClosure.ι x ≫ f) (closure_quasiSeparated f x) (closure_locallyOfFiniteType f x)
    δ inferInstance inferInstance ((Modules.pullback (PointClosure.ι x)).obj L) (Modules.isInvertibleObject_pullback (PointClosure.ι x) L) (firstChernMeromorphicSection f L x)
    (firstChernMeromorphicSection_isRegular f L x)

/-- The divisor on a point closure has the expected relative degree. -/
private theorem restrictedDivisor_mem (k : ℤ) (x : Points X)
    (hx : (relativeDimensionFunction f) δ x = k + 1) :
    restrictedDivisor f δ L x ∈ Hom.cycleGroup (PointClosure.ι x ≫ f) δ k := sorry

/-- The pushforward to `X` of the divisor of the generic meromorphic section of
`L` pulled back to the reduced closure of a point of relative dimension `k + 1`. -/
noncomputable def firstChernGeneratorCycle (k : ℤ) (x : Points X)
    (hx : Hom.relativeDimensionFunction f δ x = k + 1) :
    Function.locallyFinsupp (Points X) ℤ := by
  let _ := hx
  exact @closedImmersionCyclePushforward S (PointClosure.space x) X (PointClosure.ι x)
    (PointClosure.instIsClosedImmersion_ι x)
    (@Hom.meromorphicSectionDivisorCycle S B (PointClosure.space x) inferInstance inferInstance
      (PointClosure.ι x ≫ f) (closure_quasiSeparated f x) (closure_locallyOfFiniteType f x)
      δ inferInstance (by exact closure_integral f x)
      ((Modules.pullback (PointClosure.ι x)).obj L)
      (Modules.isInvertibleObject_pullback (PointClosure.ι x) L)
      (firstChernMeromorphicSection f L x) (firstChernMeromorphicSection_isRegular f L x))

/-- The pushed divisor of a point closure has the expected degree. -/
theorem firstChernGeneratorCycle_mem (k : ℤ) (x : Points X)
    (hx : (relativeDimensionFunction f) δ x = k + 1) :
    firstChernGeneratorCycle f δ L k x hx ∈ Hom.cycleGroup f δ k := sorry

/-- Locally finite input cycles give locally finite families of the actual
point-closure divisor cycles, in the relative dimension grading. -/
theorem firstChernGeneratorTermsLocallyFinite (k : ℤ)
    (α : Function.locallyFinsupp (Points X) ℤ) :
    LocallyFinite fun x : Points X ↦
      (if hx : relativeDimensionFunction f δ x = k + 1 then
        α x • firstChernGeneratorCycle f δ L k x hx else 0).support := sorry

/-- The locally finite sum of point-closure divisor cycles weighted by the
coefficients of `α`, using only points of relative dimension `k + 1`.
For a cycle of degree `k + 1`, this is its first Chern intersection cycle. -/
def firstChernCycle (k : ℤ) (α : Function.locallyFinsupp (Points X) ℤ) :
    Function.locallyFinsupp (Points X) ℤ :=
  AlgebraicCycle.locallyFiniteSum
    (fun x : Points X ↦ if hx : relativeDimensionFunction f δ x = k + 1 then
      α x • firstChernGeneratorCycle f δ L k x hx else 0)
    (firstChernGeneratorTermsLocallyFinite f δ L k α)

/-- First Chern intersection lowers the cycle degree by one. -/
theorem firstChernCycle_mem (k : ℤ) (α : cycleGroup f δ (k + 1)) :
    firstChernCycle f δ L k (α : Function.locallyFinsupp (Points X) ℤ) ∈ cycleGroup f δ k := sorry

/-- The Chow class of the first Chern divisor cycle. -/
private def firstChernCapValue (k : ℤ) (α : cycleGroup f δ (k + 1)) : chowGroup f δ k :=
  chowMk f δ k ⟨firstChernCycle f δ L k α, firstChernCycle_mem f δ L k α⟩

/-- The Chow class of the first Chern cycle of zero is zero. -/
private theorem firstChernClassCap_zero (k : ℤ) : firstChernCapValue f δ L k 0 = 0 := sorry

/-- The Chow class of the first Chern cycle is additive. -/
private theorem firstChernClassCap_add (k : ℤ) (α β : cycleGroup f δ (k + 1)) :
    firstChernCapValue f δ L k (α + β) = firstChernCapValue f δ L k α + firstChernCapValue f δ L k β := sorry

/-- Intersection with an invertible module sends degree-`k + 1` cycles to degree-`k` Chow classes. -/
def firstChernClassCap (k : ℤ) : cycleGroup f δ (k + 1) →+ chowGroup f δ k where
  toFun := fun α ↦
    chowMk f δ k ⟨firstChernCycle f δ L k α, firstChernCycle_mem f δ L k α⟩
  map_zero' := by exact firstChernClassCap_zero f δ L k
  map_add' := by exact firstChernClassCap_add f δ L k

/-- First Chern intersection is the Chow class of its concrete divisor cycle. -/
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
    firstChernRestrictedDivisorCycle f δ L Y i s hs ∈ cycleGroup (i ≫ f) δ k := sorry

/-- Divisor cycle on the concrete closure with explicitly scoped integrality. -/
def firstChernPointClosureDivisorCycle (x : Points X)
    (s : meromorphicSections (PointClosure.space x) ((Modules.pullback (PointClosure.ι x)).obj L))
    (hs : IsRegularMeromorphicSection (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L) s) :
    Function.locallyFinsupp (Points (PointClosure.space x)) ℤ := by
  -- Local instance justification (proof-local temporary data): Use integrality of the actual reduced closure of x to evaluate its generic line fibre and form its divisor.
  letI : AlgebraicSpace.IsIntegral (PointClosure.space x) := by exact closure_integral f x
  -- Local instance justification (proof-local temporary data): The composite of the actual point-closure inclusion with f is quasi-separated, as required by its relative divisor cycle.
  letI := closure_quasiSeparated f x
  -- Local instance justification (proof-local temporary data): The same point-closure structure morphism is locally of finite type, giving the existing relative divisor-cycle scope.
  letI := closure_locallyOfFiniteType f x
  exact firstChernRestrictedDivisorCycle f δ L (PointClosure.space x) (PointClosure.ι x) s hs

/-- The singleton cycle `[W]` of a point of relative dimension `k + 1`. -/
theorem firstChernSingleton_mem (k : ℤ) (x : Points X)
    (hx : (relativeDimensionFunction f) δ x = k + 1) :
    (@Function.locallyFinsuppWithin.single (Points X) _ ℤ (Classical.decEq _) _
        x 1) ∈ (cycleGroup f) δ (k + 1) := sorry

/-- Pushforward of a restricted divisor cycle from the reduced closure of a
degree-`k + 1` point is a `k`-cycle. -/
theorem firstChernClosedSubspacePushforward_mem (k : ℤ) (x : Points X)
    (hx : (relativeDimensionFunction f) δ x = k + 1)
    (s : meromorphicSections (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L))
    (hs : IsRegularMeromorphicSection (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L) s) :
    @closedImmersionCyclePushforward S (PointClosure.space x) X (PointClosure.ι x)
        (PointClosure.instIsClosedImmersion_ι x)
        (firstChernPointClosureDivisorCycle f δ L x s hs) ∈
      (cycleGroup f) δ k := sorry

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
        ⟨@closedImmersionCyclePushforward S (PointClosure.space x) X (PointClosure.ι x)
        (PointClosure.instIsClosedImmersion_ι x)
            (firstChernPointClosureDivisorCycle f δ L x s hs),
          firstChernClosedSubspacePushforward_mem f δ L k x hx s hs⟩ := sorry

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
        ⟨@closedImmersionCyclePushforward S (PointClosure.space x) X (PointClosure.ι x)
        (PointClosure.instIsClosedImmersion_ι x)
            (firstChernPointClosureDivisorCycle f δ L x s hs),
          firstChernClosedSubspacePushforward_mem f δ L k x hx s hs⟩ =
      (chowMk f) δ k
        ⟨@closedImmersionCyclePushforward S (PointClosure.space x) X (PointClosure.ι x)
        (PointClosure.instIsClosedImmersion_ι x)
            (firstChernPointClosureDivisorCycle f δ L x t ht),
          firstChernClosedSubspacePushforward_mem f δ L k x hx t ht⟩ := sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
