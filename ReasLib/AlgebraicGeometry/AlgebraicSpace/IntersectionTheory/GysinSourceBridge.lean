/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap82.Definition_82_26_2_ChowCohomology

/-! The public quotient Gysin map on the actual source generator [W]. -/
@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace.Hom
open Function Set TopologicalSpace
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.GysinSourceBridge

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (L : X.Modules) [isInvertibleObject L] (s : L.sections)
    (k : ℤ) (x : Points X) (hx : Hom.relativeDimensionFunction pX δ x = k + 1)

/-- Closedness of Z(s) makes containment of the reduced closure equivalent to
membership of its original point. No new geometric premise is introduced. -/
theorem contained_iff_mem :
    GysinConstruction.Contained L s x ↔ x ∈ (zeroScheme L s).pointsSet := by
  rw [GysinConstruction.contained_iff_support]
  change Set.range (Points.map (PointClosure.ι x)) ⊆ (zeroScheme L s).pointsSet ↔ _
  rw [PointClosure.range_ι, PointClosure.coe_closedSubset]
  constructor
  · intro h
    exact h (subset_closure (Set.mem_singleton x))
  · intro h
    exact closure_minimal (Set.singleton_subset_iff.mpr h) (zeroScheme L s).isClosed_pointsSet

/-- The actual degree-(k+1) generator of the input cycle group. -/
def inputGenerator : Hom.cycleGroup pX δ (k + 1) := by
  classical
  exact ⟨Function.locallyFinsuppWithin.single x 1, by
    intro y hy
    by_cases h : y = x
    · simpa only [h] using hx
    · simp [Function.locallyFinsuppWithin.single_apply, h] at hy⟩

/-- Extending the generator linearly by the existing locally finite sum really
recovers that generator, including the contained branch. -/
theorem gysinCycle_single :
    RefinedGysin.gysinCycle δ pX k L s
      (inputGenerator δ pX k x hx : Function.locallyFinsupp (Points X) ℤ) =
        RefinedGysin.gysinGeneratorCycle δ pX k L s x hx := by
  classical
  ext z
  change (∑ᶠ y : Points X,
    (if hy : Hom.relativeDimensionFunction pX δ y = k + 1 then
      ((inputGenerator δ pX k x hx).val y) • RefinedGysin.gysinGeneratorCycle δ pX k L s y hy
    else 0) z) = _
  rw [finsum_eq_single _ x]
  · simp [inputGenerator, hx, Function.locallyFinsuppWithin.single_apply]
  · intro y hy
    by_cases hdegree : Hom.relativeDimensionFunction pX δ y = k + 1
    · simp [hdegree, inputGenerator, Function.locallyFinsuppWithin.single_apply, hy]
    · simp [hdegree]

/-- The quotient map uses the concrete Chern branch on the true class [W]. -/
theorem chowGysin_generator_contained
    (hW : (ClosedSubspace.pointClosure x).pointsSet ⊆ (zeroScheme L s).pointsSet) :
    chowGysin δ pX L s k (Hom.chowMk pX δ (k + 1) (inputGenerator δ pX k x hx)) =
      Hom.chowMk (zeroSchemeι L s ≫ pX) δ k
        (GysinConstruction.containedValue δ pX L s k x hx
          ((GysinConstruction.contained_iff_support L s x).mpr hW)) := by
  change Hom.chowMk (zeroSchemeι L s ≫ pX) δ k
    (gysinCycleHom δ pX k L s (inputGenerator δ pX k x hx)) = _
  congr 1
  apply Subtype.ext
  change RefinedGysin.gysinCycle δ pX k L s (inputGenerator δ pX k x hx).val = _
  rw [gysinCycle_single]
  exact gysinGeneratorCycle_of_support_subset δ pX k L s x hx hW

-- Local instance justification (proof-local temporary data): The generator formula uses the reduced point closure over the fixed good base; install its two proved finiteness properties only in this construction.
attribute [local instance] closure_quasiSeparated closure_locallyOfFiniteType

/-- Definition82.22.1 at the actual public Chow entrypoint: induced closed
pushforward of the restricted first Chern class on the fundamental cycle. -/
theorem chowGysin_generator_source_formula
    (hW : (ClosedSubspace.pointClosure x).pointsSet ⊆ (zeroScheme L s).pointsSet) :
    chowGysin δ pX L s k (Hom.chowMk pX δ (k + 1) (inputGenerator δ pX k x hx)) =
      @properPushforward S B _ _ δ _ (PointClosure.space x) (zeroScheme L s).X
        (PointClosure.ι x ≫ pX) _ _ (zeroSchemeι L s ≫ pX) _ _
        (GysinConstruction.intoZero L s x
          ((GysinConstruction.contained_iff_support L s x).mpr hW)) _
        (GysinConstruction.intoZero_over pX L s x
          ((GysinConstruction.contained_iff_support L s x).mpr hW)) k
        (@firstChernClassCap S B (PointClosure.space x) _ _ (PointClosure.ι x ≫ pX) _ _
          δ _ ((Modules.pullback (PointClosure.ι x)).obj L)
          (Modules.isInvertibleObject_pullback (PointClosure.ι x) L) k
          (GysinConstruction.fundamental δ pX k x hx)) := by
  rw [chowGysin_generator_contained δ pX L s k x hx hW]
  exact GysinConstruction.containedValue_chowMk δ pX L s k x hx _

/-- For the zero section, all input generators use the same specified Chern
construction. This does not set c1 of a nontrivial line bundle to zero. -/
theorem chowGysin_zero_section_generator :
    chowGysin δ pX L (ZeroSchemeFactor.zeroSection L) k
      (Hom.chowMk pX δ (k + 1) (inputGenerator δ pX k x hx)) =
      Hom.chowMk (zeroSchemeι L (ZeroSchemeFactor.zeroSection L) ≫ pX) δ k
        (GysinConstruction.containedValue δ pX L (ZeroSchemeFactor.zeroSection L) k x hx
          (ZeroSchemeFactor.vanishesOn_zero L (PointClosure.ι x))) := by
  exact chowGysin_generator_contained δ pX L (ZeroSchemeFactor.zeroSection L) k x hx
    ((GysinConstruction.contained_iff_support L (ZeroSchemeFactor.zeroSection L) x).mp
      (ZeroSchemeFactor.vanishesOn_zero L (PointClosure.ι x)))

end AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.GysinSourceBridge
