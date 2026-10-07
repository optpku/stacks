module

public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.LocallyFinsupp
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.LocallyFiniteSum
public import stacks_project.Chap70.Lemma_70_5_4_PointClosure
public import stacks_project.Chap72.Definition_72_4_1_Integral
public import stacks_project.Chap82.Definition_82_15_1_Chow
public import stacks_project.Chap82.Definition_82_15_1_ClosedPushforward
public import stacks_project.Chap82.Definition_82_17_1_Cycle

/-!
# Intersection with the first Chern class on algebraic spaces

On a good algebraic space, an invertible module determines an additive operation
`c1(L) ∩ - : Z_{k+1}(X) → CH_k(X)`. On the reduced closure of a point of relative
dimension `k + 1` this is the closed-immersion pushforward of the divisor cycle of
a regular meromorphic section of the pullback module, and the operation extends
by locally finite linear combination.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open Function Set Topology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Modules

/-- Pullback of modules along a morphism of algebraic spaces preserves
tensor-invertibility. This is a theorem rather than a global instance, to avoid
clashing with later global pullback-invertibility instances. -/
theorem isInvertibleObject_pullback {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (i : X ⟶ Y) (M : Y.Modules) [isInvertibleObject M] :
    isInvertibleObject ((pullback i).obj M) :=
  sorry

end Modules

namespace Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]

/-- The reduced closure of a point is integral. -/
instance instIsIntegral_pointClosure_space (x : Points X) :
    IsIntegral (PointClosure.space x) :=
  sorry

/-- The reduced point-closure morphism remains quasi-separated after composing
with a good structure morphism. -/
instance instQuasiSeparated_pointClosure_comp (x : Points X) :
    QuasiSeparated (PointClosure.ι x ≫ f) :=
  sorry

/-- The reduced point-closure morphism remains locally of finite type after
composing with a good structure morphism. -/
instance instLocallyOfFiniteType_pointClosure_comp (x : Points X) :
    LocallyOfFiniteType (PointClosure.ι x ≫ f) :=
  sorry

variable (L : X.Modules) [isInvertibleObject L]

/-- The restriction of an invertible module to a reduced point closure has a
regular meromorphic section. -/
theorem exists_regularMeromorphicSection_pointClosure (x : Points X) :
    ∃ t : meromorphicSections (PointClosure.space x)
        ((Modules.pullback (PointClosure.ι x)).obj L),
      IsRegularMeromorphicSection (PointClosure.space x)
        ((Modules.pullback (PointClosure.ι x)).obj L) t :=
  sorry

/-- A chosen regular meromorphic section of `i^* L` on the reduced closure of
`x`. -/
noncomputable def firstChernMeromorphicSection (x : Points X) :
    meromorphicSections (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L) :=
  Classical.choose (exists_regularMeromorphicSection_pointClosure L x)

/-- The chosen meromorphic section of `i^* L` on a reduced point closure is
regular. -/
theorem firstChernMeromorphicSection_isRegular (x : Points X) :
    IsRegularMeromorphicSection (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L)
      (firstChernMeromorphicSection L x) :=
  sorry

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
    (hk : (i ≫ f).deltaDimension δ (univIrreducibleClosed Y) = k + 1)
    (s : meromorphicSections Y ((Modules.pullback i).obj L))
    (hs : IsRegularMeromorphicSection Y ((Modules.pullback i).obj L) s) :
    firstChernRestrictedDivisorCycle f δ L Y i s hs ∈ (i ≫ f).cycleGroup δ k :=
  sorry

/-- The cycle contributed by a degree-`k + 1` point: the closed-immersion
pushforward of `div_{i^* L}(s)` from the reduced closure of `x`. -/
noncomputable def firstChernGeneratorCycle (k : ℤ) (x : Points X)
    (hx : f.relativeDimensionFunction δ x = k + 1) :
    Function.locallyFinsupp (Points X) ℤ :=
  let _ := hx
  closedImmersionPushforwardCycle (ClosedSubspace.ofι (PointClosure.ι x))
    (firstChernRestrictedDivisorCycle f δ L (PointClosure.space x) (PointClosure.ι x)
      (firstChernMeromorphicSection L x)
      (firstChernMeromorphicSection_isRegular L x))

/-- The first-Chern generator cycle of a point of relative dimension `k + 1` is
a `k`-cycle. -/
theorem firstChernGeneratorCycle_mem (k : ℤ) (x : Points X)
    (hx : f.relativeDimensionFunction δ x = k + 1) :
    firstChernGeneratorCycle f δ L k x hx ∈ f.cycleGroup δ k :=
  sorry

/-- The first-Chern generator cycle is the closed-immersion pushforward of the
chosen regular meromorphic-section divisor cycle. -/
theorem firstChernGeneratorCycle_apply (k : ℤ) (x : Points X)
    (hx : f.relativeDimensionFunction δ x = k + 1) (y : Points X) :
    firstChernGeneratorCycle f δ L k x hx y =
      closedImmersionPushforwardCycle (ClosedSubspace.ofι (PointClosure.ι x))
        (firstChernRestrictedDivisorCycle f δ L (PointClosure.space x) (PointClosure.ι x)
          (firstChernMeromorphicSection L x)
          (firstChernMeromorphicSection_isRegular L x)) y :=
  sorry

/-- The coefficient-weighted first-Chern generator cycles of a degree-`k + 1`
cycle form a locally finite family on `X`. -/
theorem firstChernGeneratorTermsLocallyFinite (k : ℤ)
    (α : Function.locallyFinsupp (Points X) ℤ) :
    LocallyFinite fun x : Points X ↦
      (if hx : f.relativeDimensionFunction δ x = k + 1 then
        α x • firstChernGeneratorCycle f δ L k x hx
      else 0).support :=
  sorry

/-- The explicit locally finite cycle obtained by extending first-Chern
intersection linearly from integral point closures. -/
noncomputable def firstChernCycle (k : ℤ)
    (α : Function.locallyFinsupp (Points X) ℤ) :
    Function.locallyFinsupp (Points X) ℤ :=
  AlgebraicCycle.locallyFiniteSum
    (fun x : Points X ↦
      if hx : f.relativeDimensionFunction δ x = k + 1 then
        α x • firstChernGeneratorCycle f δ L k x hx
      else 0)
    (firstChernGeneratorTermsLocallyFinite f δ L k α)

/-- Coefficients of the first-Chern cycle are the pointwise finite sums of the
weighted generator cycles. -/
theorem firstChernCycle_apply (k : ℤ)
    (α : Function.locallyFinsupp (Points X) ℤ) (y : Points X) :
    firstChernCycle f δ L k α y =
      ∑ᶠ x : Points X,
        (if hx : f.relativeDimensionFunction δ x = k + 1 then
          α x • firstChernGeneratorCycle f δ L k x hx
        else 0) y :=
  sorry

/-- The first-Chern cycle of a `(k + 1)`-cycle is a `k`-cycle. -/
theorem firstChernCycle_mem (k : ℤ) (α : f.cycleGroup δ (k + 1)) :
    firstChernCycle f δ L k (α : Function.locallyFinsupp (Points X) ℤ) ∈
      f.cycleGroup δ k :=
  sorry

/-- The first-Chern cycle construction preserves addition of underlying cycles. -/
theorem firstChernCycle_add (k : ℤ)
    (α β : Function.locallyFinsupp (Points X) ℤ) :
    firstChernCycle f δ L k (α + β) =
      firstChernCycle f δ L k α + firstChernCycle f δ L k β :=
  sorry

/-- The Chow class of the first-Chern cycle of the zero cycle vanishes. -/
theorem firstChernClassCap_zero (k : ℤ) :
    f.chowMk δ k
        ⟨firstChernCycle f δ L k (0 : Function.locallyFinsupp (Points X) ℤ),
          firstChernCycle_mem f δ L k 0⟩ =
      0 :=
  sorry

/-- Taking the Chow class of the first-Chern cycle preserves addition. -/
theorem firstChernClassCap_add (k : ℤ) (α β : f.cycleGroup δ (k + 1)) :
    f.chowMk δ k
        ⟨firstChernCycle f δ L k
          ((α + β : f.cycleGroup δ (k + 1)) :
            Function.locallyFinsupp (Points X) ℤ),
          firstChernCycle_mem f δ L k (α + β)⟩ =
      f.chowMk δ k
          ⟨firstChernCycle f δ L k (α : Function.locallyFinsupp (Points X) ℤ),
            firstChernCycle_mem f δ L k α⟩ +
        f.chowMk δ k
          ⟨firstChernCycle f δ L k (β : Function.locallyFinsupp (Points X) ℤ),
            firstChernCycle_mem f δ L k β⟩ :=
  sorry

/-- Intersection with the first Chern class of an invertible module, as an
additive map `c1(L) ∩ - : Z_{k+1}(X) → CH_k(X)`. -/
noncomputable def firstChernClassCap (k : ℤ) :
    f.cycleGroup δ (k + 1) →+ f.chowGroup δ k where
  toFun := fun α ↦
    f.chowMk δ k
      ⟨firstChernCycle f δ L k (α : Function.locallyFinsupp (Points X) ℤ),
        firstChernCycle_mem f δ L k α⟩
  map_zero' := firstChernClassCap_zero f δ L k
  map_add' := firstChernClassCap_add f δ L k

/-- The first-Chern cap map is computed by the explicit locally finite cycle
followed by the canonical map to `CH_k(X)`. -/
theorem firstChernClassCap_apply (k : ℤ) (α : f.cycleGroup δ (k + 1)) :
    firstChernClassCap f δ L k α =
      f.chowMk δ k
        ⟨firstChernCycle f δ L k (α : Function.locallyFinsupp (Points X) ℤ),
          firstChernCycle_mem f δ L k α⟩ :=
  sorry

/-- The singleton cycle `[W]` of a point of relative dimension `k + 1`. -/
theorem firstChernSingleton_mem (k : ℤ) (x : Points X)
    (hx : f.relativeDimensionFunction δ x = k + 1) :
    (@Function.locallyFinsuppWithin.single (Points X) _ ℤ (Classical.decEq _) _
        x 1) ∈ f.cycleGroup δ (k + 1) :=
  sorry

/-- Pushforward of a restricted divisor cycle from the reduced closure of a
degree-`k + 1` point is a `k`-cycle. -/
theorem firstChernClosedSubspacePushforward_mem (k : ℤ) (x : Points X)
    (hx : f.relativeDimensionFunction δ x = k + 1)
    (s : meromorphicSections (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L))
    (hs : IsRegularMeromorphicSection (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L) s) :
    closedImmersionPushforwardCycle (ClosedSubspace.ofι (PointClosure.ι x))
        (firstChernRestrictedDivisorCycle f δ L (PointClosure.space x)
          (PointClosure.ι x) s hs) ∈
      f.cycleGroup δ k :=
  sorry

/-- On the reduced integral closed subspace `i : W → X` of a point of
relative dimension `k + 1`, `c1(L) ∩ [W]` is the Chow class of
`i_* div_{i^* L}(s)` for any regular meromorphic section of `i^* L`. -/
theorem firstChernClassCap_closedSubspace (k : ℤ) (x : Points X)
    (hx : f.relativeDimensionFunction δ x = k + 1)
    (s : meromorphicSections (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L))
    (hs : IsRegularMeromorphicSection (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L) s) :
    firstChernClassCap f δ L k
        ⟨@Function.locallyFinsuppWithin.single (Points X) _ ℤ
            (Classical.decEq _) _ x 1,
          firstChernSingleton_mem f δ k x hx⟩ =
      f.chowMk δ k
        ⟨closedImmersionPushforwardCycle (ClosedSubspace.ofι (PointClosure.ι x))
            (firstChernRestrictedDivisorCycle f δ L (PointClosure.space x)
              (PointClosure.ι x) s hs),
          firstChernClosedSubspacePushforward_mem f δ L k x hx s hs⟩ :=
  sorry

/-- The Chow class of `i_* div_{i^* L}(s)` on the reduced closure of a
degree-`k + 1` point is independent of the choice of regular meromorphic
section of `i^* L`. -/
theorem firstChernClassCap_eq_of_meromorphicSection (k : ℤ) (x : Points X)
    (hx : f.relativeDimensionFunction δ x = k + 1)
    (s : meromorphicSections (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L))
    (hs : IsRegularMeromorphicSection (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L) s)
    (t : meromorphicSections (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L))
    (ht : IsRegularMeromorphicSection (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L) t) :
    f.chowMk δ k
        ⟨closedImmersionPushforwardCycle (ClosedSubspace.ofι (PointClosure.ι x))
            (firstChernRestrictedDivisorCycle f δ L (PointClosure.space x)
              (PointClosure.ι x) s hs),
          firstChernClosedSubspacePushforward_mem f δ L k x hx s hs⟩ =
      f.chowMk δ k
        ⟨closedImmersionPushforwardCycle (ClosedSubspace.ofι (PointClosure.ι x))
            (firstChernRestrictedDivisorCycle f δ L (PointClosure.space x)
              (PointClosure.ι x) t ht),
          firstChernClosedSubspacePushforward_mem f δ L k x hx t ht⟩ :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
