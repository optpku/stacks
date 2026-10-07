module

public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Topology.LocallyFinsupp
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.LocallyFiniteSum
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap70.Lemma_70_5_4_PointClosure
public import stacks_project.Chap72.Lemma_72_7_5
public import stacks_project.Chap82.Definition_82_2_5_DeltaDimension
public import stacks_project.Chap82.Definition_82_3_1_CycleGroup

/-!
# Tensor and unit identities for first-Chern cap on algebraic spaces

On a good algebraic space, intersection with the first Chern class of an
invertible module is additive in the sheaf, and vanishes on the tensor unit.
These identities are properties of `Hom.firstChernClassCap`, valued in the
Chow group `chowGroup f δ k`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicCycle Function Set Topology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The reduced closure of a point is integral. -/
instance instIsIntegral_pointClosure_space {S : Scheme.{u}} {X : AlgebraicSpace S}
    (x : Points X) : IsIntegral (PointClosure.space x) :=
  sorry

/-- The reduced closure of a point is decent. -/
instance instIsDecent_pointClosure_space {S : Scheme.{u}} {X : AlgebraicSpace S}
    (x : Points X) : IsDecent (PointClosure.space x) :=
  sorry

/-- The reduced closure of a point is locally Noetherian when `X` is locally
Noetherian. -/
instance instIsLocallyNoetherian_pointClosure_space {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsLocallyNoetherian X] (x : Points X) :
    IsLocallyNoetherian (PointClosure.space x) :=
  sorry

namespace Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]

/-- A good morphism is locally of finite type over a locally Noetherian base,
so the source is locally Noetherian. -/
instance instIsLocallyNoetherian_ofGood : IsLocallyNoetherian X :=
  sorry

/-- Weight-1 pushforward of a locally finite cycle along a morphism of algebraic
spaces, summing coefficients on fibres of `Points.map`. -/
def closedImmersionPushforwardCycle {Y : AlgebraicSpace S} (i : Y ⟶ X)
    (α : Function.locallyFinsupp (Points Y) ℤ) :
    Function.locallyFinsupp (Points X) ℤ where
  toFun := fun x ↦ ∑ᶠ y ∈ Points.map i ⁻¹' {x}, α y
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' := sorry

/-- Closed-immersion pushforward evaluates by a weight-1 finsum on the fibre. -/
theorem closedImmersionPushforwardCycle_apply {Y : AlgebraicSpace S} (i : Y ⟶ X)
    (α : Function.locallyFinsupp (Points Y) ℤ) (x : Points X) :
    closedImmersionPushforwardCycle i α x =
      ∑ᶠ y ∈ Points.map i ⁻¹' {x}, α y :=
  sorry

/-- The singleton cycles at generic points of the prime divisors of a Weil
divisor form a locally finite family. -/
theorem weilDivisorCycle_locallyFinite {Y : AlgebraicSpace S} [IsDecent Y]
    (D : WeilDivisor Y) :
    LocallyFinite fun Z : PrimeDivisor Y ↦
      (@locallyFinsuppWithin.single (Points Y) _ ℤ (Classical.decEq _) _
        Z.genericPoint (D.coeff Z)).support :=
  sorry

/-- Convert a Weil divisor to the locally finite cycle carrying each coefficient
at the generic point of the corresponding prime divisor. -/
noncomputable def weilDivisorCycle {Y : AlgebraicSpace S} [IsDecent Y]
    (D : WeilDivisor Y) : Function.locallyFinsupp (Points Y) ℤ :=
  locallyFiniteSum
    (fun Z : PrimeDivisor Y ↦
      @locallyFinsuppWithin.single (Points Y) _ ℤ (Classical.decEq _) _
        Z.genericPoint (D.coeff Z))
    (weilDivisorCycle_locallyFinite D)

/-- The Weil-divisor cycle is the locally finite sum of its prime-divisor
singleton cycles. -/
theorem weilDivisorCycle_eq {Y : AlgebraicSpace S} [IsDecent Y]
    (D : WeilDivisor Y) :
    weilDivisorCycle D =
      locallyFiniteSum
        (fun Z : PrimeDivisor Y ↦
          @locallyFinsuppWithin.single (Points Y) _ ℤ (Classical.decEq _) _
            Z.genericPoint (D.coeff Z))
        (weilDivisorCycle_locallyFinite D) :=
  sorry

/-- Pullback of modules along a morphism of algebraic spaces preserves
tensor-invertibility. -/
instance instIsInvertibleObject_pullback {Y : AlgebraicSpace S} (i : Y ⟶ X)
    (M : X.Modules) [isInvertibleObject M] :
    isInvertibleObject ((Modules.pullback i).obj M) :=
  sorry

/-- The restriction of an invertible module to a reduced point closure has a
regular meromorphic section. -/
theorem exists_regularMeromorphicSection_pointClosure (L : X.Modules)
    [isInvertibleObject L] (x : Points X) :
    ∃ t : meromorphicSections (PointClosure.space x)
        ((Modules.pullback (PointClosure.ι x)).obj L),
      IsRegularMeromorphicSection (PointClosure.space x)
        ((Modules.pullback (PointClosure.ι x)).obj L) t :=
  sorry

/-- A chosen regular meromorphic section of `i^* L` on the reduced closure of
`x`. -/
noncomputable def firstChernMeromorphicSection (L : X.Modules)
    [isInvertibleObject L] (x : Points X) :
    meromorphicSections (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L) :=
  Classical.choose (exists_regularMeromorphicSection_pointClosure L x)

/-- The chosen meromorphic section of `i^* L` on a reduced point closure is
regular. -/
theorem firstChernMeromorphicSection_isRegular (L : X.Modules)
    [isInvertibleObject L] (x : Points X) :
    IsRegularMeromorphicSection (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L)
      (firstChernMeromorphicSection L x) :=
  sorry

/-- The cycle contributed by a degree-`k + 1` point: the closed-immersion
pushforward of `div_{i^* L}(s)` from the reduced closure of `x`. -/
noncomputable def firstChernGeneratorCycle (L : X.Modules)
    [isInvertibleObject L] (k : ℤ) (x : Points X)
    (hx : relativeDimensionFunction f δ x = k + 1) :
    Function.locallyFinsupp (Points X) ℤ :=
  let _ := hx
  closedImmersionPushforwardCycle (PointClosure.ι x)
    (weilDivisorCycle
      (nonzeroMeromorphicSectionWeilDivisor
        (firstChernMeromorphicSection L x)
        (firstChernMeromorphicSection_isRegular L x)))

/-- The coefficient-weighted first-Chern generator cycles of a degree-`k + 1`
cycle form a locally finite family on `X`. -/
theorem firstChernGeneratorTermsLocallyFinite (L : X.Modules)
    [isInvertibleObject L] (k : ℤ) (α : Function.locallyFinsupp (Points X) ℤ) :
    LocallyFinite fun x : Points X ↦
      (if hx : relativeDimensionFunction f δ x = k + 1 then
        α x • firstChernGeneratorCycle f δ L k x hx
      else 0).support :=
  sorry

/-- The explicit locally finite cycle obtained by extending first-Chern
intersection linearly from integral point closures. -/
noncomputable def firstChernCycle (L : X.Modules) [isInvertibleObject L] (k : ℤ)
    (α : Function.locallyFinsupp (Points X) ℤ) :
    Function.locallyFinsupp (Points X) ℤ :=
  locallyFiniteSum
    (fun x : Points X ↦
      if hx : relativeDimensionFunction f δ x = k + 1 then
        α x • firstChernGeneratorCycle f δ L k x hx
      else 0)
    (firstChernGeneratorTermsLocallyFinite f δ L k α)

/-- Coefficients of the first-Chern cycle are the pointwise finite sums of the
weighted generator cycles. -/
theorem firstChernCycle_apply (L : X.Modules) [isInvertibleObject L] (k : ℤ)
    (α : Function.locallyFinsupp (Points X) ℤ) (y : Points X) :
    firstChernCycle f δ L k α y =
      ∑ᶠ x : Points X,
        (if hx : relativeDimensionFunction f δ x = k + 1 then
          α x • firstChernGeneratorCycle f δ L k x hx
        else 0) y :=
  sorry

/-- The first-Chern cycle of a `(k + 1)`-cycle is a `k`-cycle. -/
theorem firstChernCycle_mem (L : X.Modules) [isInvertibleObject L] (k : ℤ)
    (α : cycleGroup f δ (k + 1)) :
    firstChernCycle f δ L k (α : Function.locallyFinsupp (Points X) ℤ) ∈
      cycleGroup f δ k :=
  sorry

/-- Principal cycles `i_* div(φ)` on reduced point closures of relative
dimension `k + 1`. -/
def rationalEquivalenceGenerators (k : ℤ) : Set (cycleGroup f δ k) :=
  {α | ∃ (x : Points X) (φ : (RationalFunction (PointClosure.space x))ˣ),
    relativeDimensionFunction f δ x = k + 1 ∧
      (α : Function.locallyFinsupp (Points X) ℤ) =
        closedImmersionPushforwardCycle (PointClosure.ι x)
          (weilDivisorCycle (WeilDivisor.ofRationalUnit φ))}

/-- Membership in the generating set of rational equivalence is the existence of
a principal point-closure pushforward. -/
theorem mem_rationalEquivalenceGenerators (k : ℤ) (α : cycleGroup f δ k) :
    α ∈ rationalEquivalenceGenerators f δ k ↔
      ∃ (x : Points X) (φ : (RationalFunction (PointClosure.space x))ˣ),
        relativeDimensionFunction f δ x = k + 1 ∧
          (α : Function.locallyFinsupp (Points X) ℤ) =
            closedImmersionPushforwardCycle (PointClosure.ι x)
              (weilDivisorCycle (WeilDivisor.ofRationalUnit φ)) :=
  sorry

/-- Principal cycles on reduced point closures of relative dimension `k + 1`
generate rational equivalence in `Z_k(X)`. -/
noncomputable def rationalEquivalenceBoundaries (k : ℤ) :
    AddSubgroup (cycleGroup f δ k) :=
  AddSubgroup.closure (rationalEquivalenceGenerators f δ k)

/-- Membership in the rational-equivalence subgroup means the cycle lies in the
closure of principal point-closure pushforwards. -/
theorem mem_rationalEquivalenceBoundaries (k : ℤ) (α : cycleGroup f δ k) :
    α ∈ rationalEquivalenceBoundaries f δ k ↔
      α ∈ AddSubgroup.closure (rationalEquivalenceGenerators f δ k) :=
  sorry

/-- The Chow group `CH_k(X)` of `k`-cycles modulo rational equivalence. -/
noncomputable abbrev chowGroup (k : ℤ) :=
  cycleGroup f δ k ⧸ rationalEquivalenceBoundaries f δ k

/-- The Chow group is the quotient of `Z_k(X)` by rational equivalence. -/
theorem chowGroup_eq (k : ℤ) :
    chowGroup f δ k =
      (cycleGroup f δ k ⧸ rationalEquivalenceBoundaries f δ k) :=
  sorry

/-- The canonical quotient map `Z_k(X) → CH_k(X)`. -/
noncomputable abbrev chowMk (k : ℤ) : cycleGroup f δ k →+ chowGroup f δ k :=
  QuotientAddGroup.mk' (rationalEquivalenceBoundaries f δ k)

/-- Intersection with the first Chern class of an invertible module, as an
additive map `c1(L) ∩ - : Z_{k+1}(X) → CH_k(X)`. -/
noncomputable def firstChernClassCap (L : X.Modules) [isInvertibleObject L]
    (k : ℤ) : cycleGroup f δ (k + 1) →+ chowGroup f δ k where
  toFun := fun α ↦
    chowMk f δ k ⟨firstChernCycle f δ L k (α : Function.locallyFinsupp (Points X) ℤ),
      firstChernCycle_mem f δ L k α⟩
  map_zero' := sorry
  map_add' := sorry

/-- The first-Chern cap map is computed by the explicit locally finite cycle
followed by the canonical map to `CH_k(X)`. -/
theorem firstChernClassCap_apply (L : X.Modules) [isInvertibleObject L] (k : ℤ)
    (α : cycleGroup f δ (k + 1)) :
    firstChernClassCap f δ L k α =
      chowMk f δ k
        ⟨firstChernCycle f δ L k (α : Function.locallyFinsupp (Points X) ℤ),
          firstChernCycle_mem f δ L k α⟩ :=
  sorry

/-- First-Chern cap is additive in the invertible sheaf: intersecting a
`(k + 1)`-cycle with `c1(L ⊗ N)` equals the sum of the intersections with
`c1(L)` and `c1(N)` in `CH_k(X)`. -/
theorem firstChernClassCap_tensor (L N : X.Modules) [isInvertibleObject L]
    [isInvertibleObject N] (k : ℤ) (α : cycleGroup f δ (k + 1)) :
    firstChernClassCap f δ L k α + firstChernClassCap f δ N k α =
      firstChernClassCap f δ (L ⊗ N) k α :=
  sorry

/-- First-Chern cap against the structure sheaf vanishes: intersecting any
`(k + 1)`-cycle with `c1(𝟙_ X.Modules)` is `0` in `CH_k(X)`. -/
theorem firstChernClassCap_tensorUnit (k : ℤ) (α : cycleGroup f δ (k + 1)) :
    firstChernClassCap f δ (𝟙_ X.Modules) k α = 0 :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
