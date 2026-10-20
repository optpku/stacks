module

public import stacks_project.Chap82.Definition_82_26_2_ChowCohomology
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.LocallyFinsupp
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.LocallyFiniteSum
public import stacks_project.Chap68.Lemma_68_12_8_Decent
public import stacks_project.Chap70.Lemma_70_5_4_PointClosure
public import stacks_project.Chap71.Definition_71_6_1_EffectiveCartier
public import stacks_project.Chap71.Definition_71_7_6_ZeroScheme
public import stacks_project.Chap72.Definition_72_4_1_Integral
public import stacks_project.Chap82.Definition_82_15_1_Chow
public import stacks_project.Chap82.Definition_82_15_1_ClosedPushforward
public import stacks_project.Chap82.Definition_82_22_1_Chow
public import stacks_project.Chap82.Definition_82_22_1_Intersection

/-!
# Refined Gysin maps for zero schemes of invertible modules

On a good algebraic space, a global section of an invertible module determines a
refined Gysin homomorphism from `(k + 1)`-cycles on `X` to `CH_k` of the zero
scheme, together with Cartier intersection when the zero scheme is an effective
Cartier divisor.
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
clashing with `Modules.instIsInvertibleObject_pullback`. -/
theorem isInvertibleObject_map_pullback {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (i : X ⟶ Y) (M : Y.Modules) [isInvertibleObject M] :
    isInvertibleObject ((pullback i).obj M) :=
  sorry

end Modules

namespace Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]

-- Local instance justification (proof-local temporary data): The generator formula uses the reduced point closure over the fixed good base; install its two proved finiteness properties only in this construction.
attribute [local instance] closure_quasiSeparated closure_locallyOfFiniteType

variable (k : ℤ)

/-- The generator cycle of an integral closed subspace of relative dimension
`k + 1`. -/
noncomputable def pointCycle (x : Points X) :
    Function.locallyFinsupp (Points X) ℤ :=
  @Function.locallyFinsuppWithin.single (Points X) _ ℤ (Classical.decEq _) _ x 1

/-- The generator cycle of a point of relative dimension `k + 1` is a
`(k + 1)`-cycle. -/
theorem pointCycle_mem (x : Points X)
    (hx : Hom.relativeDimensionFunction f δ x = k + 1) :
    pointCycle x ∈ Hom.cycleGroup f δ (k + 1) := by
  classical
  intro y hy
  by_cases h : y = x
  · simpa only [h] using hx
  · simp [pointCycle, Function.locallyFinsuppWithin.single_apply, h] at hy

variable (L : X.Modules) [isInvertibleObject L] (s : L.sections)

/-- Closedness of `Z(s)` makes containment of the reduced closure `W` of `x`
equivalent to membership of `x` itself. No new geometric premise is introduced. -/
theorem GysinConstruction.contained_iff_mem (x : Points X) :
    GysinConstruction.Contained L s x ↔ x ∈ (zeroScheme L s).pointsSet := by
  rw [GysinConstruction.contained_iff_support]
  change Set.range (Points.map (PointClosure.ι x)) ⊆ (zeroScheme L s).pointsSet ↔ _
  rw [PointClosure.range_ι, PointClosure.coe_closedSubset]
  constructor
  · intro h
    exact h (subset_closure (Set.mem_singleton x))
  · intro h
    exact closure_minimal (Set.singleton_subset_iff.mpr h) (zeroScheme L s).isClosed_pointsSet

/-- A point of `Z(s)` has an induced closed immersion from its reduced closure
in `X` into `Z(s)`, factoring the canonical immersion into `X`. -/
theorem exists_gysinContainedImmersion (x : Points X)
    (hx : x ∈ (zeroScheme L s).pointsSet) :
    ∃ i' : PointClosure.space x ⟶ (zeroScheme L s).X,
      i' ≫ zeroSchemeι L s = PointClosure.ι x ∧ IsClosedImmersion i' := by
  let h := (GysinConstruction.contained_iff_mem L s x).mpr hx
  exact ⟨GysinConstruction.intoZero L s x h,
    GysinConstruction.intoZero_ι L s x h, GysinConstruction.intoZero_isClosedImmersion L s x h⟩

/-- The induced closed immersion `i' : closure({x}) ⟶ Z(s)` of a point contained
in the zero scheme. -/
noncomputable def gysinContainedImmersion (x : Points X)
    (hx : x ∈ (zeroScheme L s).pointsSet) :
    PointClosure.space x ⟶ (zeroScheme L s).X :=
  GysinConstruction.intoZero L s x
    ((GysinConstruction.contained_iff_mem L s x).mpr hx)

/-- The induced immersion into `Z(s)` factors the reduced point-closure
immersion. -/
theorem gysinContainedImmersion_comp (x : Points X)
    (hx : x ∈ (zeroScheme L s).pointsSet) :
    gysinContainedImmersion L s x hx ≫ zeroSchemeι L s = PointClosure.ι x :=
  GysinConstruction.intoZero_ι L s x _

/-- The induced map from a contained reduced point closure to `Z(s)` is a closed
immersion. -/
instance instIsClosedImmersion_gysinContainedImmersion (x : Points X)
    (hx : x ∈ (zeroScheme L s).pointsSet) :
    IsClosedImmersion (gysinContainedImmersion L s x hx) :=
  GysinConstruction.intoZero_isClosedImmersion L s x
    ((GysinConstruction.contained_iff_mem L s x).mpr hx)

/-- Legacy name delegates to the constructed generic section on the actual closure. -/
noncomputable def gysinContainedSection (x : Points X) :
    meromorphicSections (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L) :=
  firstChernMeromorphicSection f L x

theorem gysinContainedSection_isRegular (x : Points X) :
    IsRegularMeromorphicSection (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L)
      (gysinContainedSection f L x) :=
  firstChernMeromorphicSection_isRegular f L x

/-- The divisor cycle of a regular meromorphic section of the restriction of `L`
to the reduced closure of `x`. -/
noncomputable def meromorphicSectionDivisorCycle_pointClosure (x : Points X)
    (t : meromorphicSections (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L))
    (ht : IsRegularMeromorphicSection (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L) t) :
    Function.locallyFinsupp (Points (PointClosure.space x)) ℤ :=
  firstChernPointClosureDivisorCycle f δ L x t ht

/-- The divisor cycle of a regular meromorphic section on a reduced point
closure of relative dimension `k + 1` is a `k`-cycle. -/
theorem meromorphicSectionDivisorCycle_pointClosure_mem (x : Points X)
    (hx : Hom.relativeDimensionFunction f δ x = k + 1)
    (t : meromorphicSections (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L))
    (ht : IsRegularMeromorphicSection (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L) t) :
    meromorphicSectionDivisorCycle_pointClosure f δ L x t ht ∈
      Hom.cycleGroup (PointClosure.ι x ≫ f) δ k :=
  sorry

/-- The pushforward to `Z(s)` of a regular meromorphic-section divisor cycle
along an induced closed immersion `i' : closure({x}) ⟶ Z(s)`. -/
noncomputable def gysinContainedCycle (x : Points X)
    (i' : PointClosure.space x ⟶ (zeroScheme L s).X) [IsClosedImmersion i']
    (t : meromorphicSections (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L))
    (ht : IsRegularMeromorphicSection (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L) t) :
    Function.locallyFinsupp (Points (zeroScheme L s).X) ℤ :=
  closedImmersionPushforwardCycle (ClosedSubspace.ofι i')
    (meromorphicSectionDivisorCycle_pointClosure f δ L x t ht)

/-- The pushed divisor cycle of a contained generator is a `k`-cycle on
`Z(s)`. -/
theorem gysinContainedCycle_mem (x : Points X)
    (hx : Hom.relativeDimensionFunction f δ x = k + 1)
    (i' : PointClosure.space x ⟶ (zeroScheme L s).X) [IsClosedImmersion i']
    (hi' : i' ≫ zeroSchemeι L s = PointClosure.ι x)
    (t : meromorphicSections (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L))
    (ht : IsRegularMeromorphicSection (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L) t) :
    gysinContainedCycle f δ L s x i' t ht ∈
      Hom.cycleGroup (zeroSchemeι L s ≫ f) δ k :=
  sorry

/-- The cycle on `Z(s)` contributed by a degree-`k + 1` point of `X`. Off the
zero scheme this is the associated cycle of `Z(s) ∩ closure({x})`; on the zero
scheme it is the pushforward along the induced closed immersion of a regular
meromorphic-section divisor cycle of `L` on that point closure. -/
noncomputable abbrev gysinGeneratorCycle (x : Points X)
    (hx : Hom.relativeDimensionFunction f δ x = k + 1) :
    Function.locallyFinsupp (Points (zeroScheme L s).X) ℤ :=
  RefinedGysin.gysinGeneratorCycle δ f k L s x hx

/-- Off `Z(s)`, the Gysin generator is the associated cycle of
`Z(s) ∩ closure({x})`. -/
theorem gysinGeneratorCycle_of_not_mem (x : Points X)
    (hx : Hom.relativeDimensionFunction f δ x = k + 1)
    (hmem : x ∉ (zeroScheme L s).pointsSet) :
    gysinGeneratorCycle f δ k L s x hx = gysinIntersectionCycle f δ k L s x := by
  classical
  have h : ¬GysinConstruction.Contained L s x :=
    fun hc ↦ hmem ((GysinConstruction.contained_iff_mem L s x).mp hc)
  simp only [gysinGeneratorCycle, RefinedGysin.gysinGeneratorCycle, dif_neg h]
  rfl

/-- On `Z(s)`, the Gysin generator is the pushforward of the chosen regular
meromorphic-section divisor cycle along the induced closed immersion into
`Z(s)`. -/
theorem gysinGeneratorCycle_of_mem (x : Points X)
    (hx : Hom.relativeDimensionFunction f δ x = k + 1)
    (hmem : x ∈ (zeroScheme L s).pointsSet) :
    gysinGeneratorCycle f δ k L s x hx =
      (GysinConstruction.containedValue δ f L s k x hx
        ((GysinConstruction.contained_iff_mem L s x).mpr hmem)).val := by
  classical
  simp only [gysinGeneratorCycle, RefinedGysin.gysinGeneratorCycle,
    dif_pos ((GysinConstruction.contained_iff_mem L s x).mpr hmem)]

/-- The coefficient-weighted Gysin generator cycles of a degree-`k + 1` cycle
form a locally finite family on `Z(s)`. -/
theorem gysinGeneratorTermsLocallyFinite
    (α : Function.locallyFinsupp (Points X) ℤ) :
    LocallyFinite fun x : Points X ↦
      (if hx : Hom.relativeDimensionFunction f δ x = k + 1 then
        α x • gysinGeneratorCycle f δ k L s x hx else 0).support :=
  RefinedGysin.gysinGeneratorTermsLocallyFinite δ f k L s α

/-- Legacy f-before-delta argument order, with the single canonical cycle producer. -/
noncomputable abbrev gysinCycle (α : Function.locallyFinsupp (Points X) ℤ) :
    Function.locallyFinsupp (Points (zeroScheme L s).X) ℤ :=
  RefinedGysin.gysinCycle δ f k L s α

/-- Coefficients of the Gysin cycle are the pointwise finite sums of the
weighted generator cycles. -/
theorem gysinCycle_apply (α : Function.locallyFinsupp (Points X) ℤ)
    (z : Points (zeroScheme L s).X) :
    gysinCycle f δ k L s α z =
      ∑ᶠ x : Points X,
        (if hx : Hom.relativeDimensionFunction f δ x = k + 1 then
          α x • gysinGeneratorCycle f δ k L s x hx
        else 0) z :=
  rfl

/-- The Gysin cycle of a `(k + 1)`-cycle is a `k`-cycle on `Z(s)`. -/
theorem gysinCycle_mem (α : Hom.cycleGroup f δ (k + 1)) :
    gysinCycle f δ k L s (α : Function.locallyFinsupp (Points X) ℤ) ∈
      Hom.cycleGroup (zeroSchemeι L s ≫ f) δ k :=
  RefinedGysin.gysinCycle_mem δ f k L s α

/-- Rule (2) on a single generator: the locally finite extension of the
generator cycles sends `[W]` to the generator cycle of `W`, in both branches. -/
theorem gysinCycle_pointCycle (x : Points X)
    (hx : Hom.relativeDimensionFunction f δ x = k + 1) :
    gysinCycle f δ k L s (pointCycle x) = gysinGeneratorCycle f δ k L s x hx := by
  classical
  ext z
  change (∑ᶠ y : Points X,
    (if hy : Hom.relativeDimensionFunction f δ y = k + 1 then
      pointCycle x y • RefinedGysin.gysinGeneratorCycle δ f k L s y hy
    else 0) z) = _
  rw [finsum_eq_single _ x]
  · simp [pointCycle, hx, Function.locallyFinsuppWithin.single_apply]
  · intro y hy
    by_cases hdegree : Hom.relativeDimensionFunction f δ y = k + 1
    · simp [hdegree, pointCycle, Function.locallyFinsuppWithin.single_apply, hy]
    · simp [hdegree]

/-- Rule (1)(b) at the Chow level: if `W ⊆ Z(s)`, the quotient Gysin map sends
`[W]` to the class of the concrete contained-branch cycle. -/
theorem chowGysin_pointCycle_of_support_subset (x : Points X)
    (hx : Hom.relativeDimensionFunction f δ x = k + 1)
    (hW : (ClosedSubspace.pointClosure x).pointsSet ⊆ (zeroScheme L s).pointsSet) :
    chowGysin δ f L s k (Hom.chowMk f δ (k + 1) ⟨pointCycle x, pointCycle_mem f δ k x hx⟩) =
      Hom.chowMk (zeroSchemeι L s ≫ f) δ k
        (GysinConstruction.containedValue δ f L s k x hx
          ((GysinConstruction.contained_iff_support L s x).mpr hW)) := by
  change Hom.chowMk (zeroSchemeι L s ≫ f) δ k
    (gysinCycleHom δ f k L s ⟨pointCycle x, pointCycle_mem f δ k x hx⟩) = _
  congr 1
  apply Subtype.ext
  change gysinCycle f δ k L s (pointCycle x) = _
  rw [gysinCycle_pointCycle f δ k L s x hx]
  exact gysinGeneratorCycle_of_support_subset δ f k L s x hx hW

/-- Rule (1)(b) in the source's form: for `W ⊆ Z(s)`, `i^*[W]` is
`i'_*(c_1(L|_W) ∩ [W])`, with `i' : W → Z(s)` the induced closed immersion. -/
theorem chowGysin_pointCycle_eq_pushforward_firstChernClassCap (x : Points X)
    (hx : Hom.relativeDimensionFunction f δ x = k + 1)
    (hW : (ClosedSubspace.pointClosure x).pointsSet ⊆ (zeroScheme L s).pointsSet) :
    chowGysin δ f L s k (Hom.chowMk f δ (k + 1) ⟨pointCycle x, pointCycle_mem f δ k x hx⟩) =
      @properPushforward S B _ _ δ _ (PointClosure.space x) (zeroScheme L s).X
        (PointClosure.ι x ≫ f) _ _ (zeroSchemeι L s ≫ f) _ _
        (GysinConstruction.intoZero L s x
          ((GysinConstruction.contained_iff_support L s x).mpr hW)) _
        (GysinConstruction.intoZero_over f L s x
          ((GysinConstruction.contained_iff_support L s x).mpr hW)) k
        (@firstChernClassCap S B (PointClosure.space x) _ _ (PointClosure.ι x ≫ f) _ _
          δ _ ((Modules.pullback (PointClosure.ι x)).obj L)
          (Modules.isInvertibleObject_pullback (PointClosure.ι x) L) k
          (GysinConstruction.fundamental δ f k x hx)) := by
  rw [chowGysin_pointCycle_of_support_subset f δ k L s x hx hW]
  exact GysinConstruction.containedValue_chowMk δ f L s k x hx _

/-- For the zero section every generator lies in the contained branch, so the
quotient Gysin map uses the restricted first Chern class there. This does not
claim that `c_1` of a nontrivial invertible module vanishes. -/
theorem chowGysin_zeroSection_pointCycle (x : Points X)
    (hx : Hom.relativeDimensionFunction f δ x = k + 1) :
    chowGysin δ f L (IntersectionTheory.ZeroSchemeFactor.zeroSection L) k
        (Hom.chowMk f δ (k + 1) ⟨pointCycle x, pointCycle_mem f δ k x hx⟩) =
      Hom.chowMk (zeroSchemeι L (IntersectionTheory.ZeroSchemeFactor.zeroSection L) ≫ f) δ k
        (GysinConstruction.containedValue δ f L (IntersectionTheory.ZeroSchemeFactor.zeroSection L) k x hx
          (IntersectionTheory.ZeroSchemeFactor.vanishesOn_zero L (PointClosure.ι x))) :=
  chowGysin_pointCycle_of_support_subset f δ k L (IntersectionTheory.ZeroSchemeFactor.zeroSection L) x hx
    ((GysinConstruction.contained_iff_support L (IntersectionTheory.ZeroSchemeFactor.zeroSection L) x).mp
      (IntersectionTheory.ZeroSchemeFactor.vanishesOn_zero L (PointClosure.ι x)))

/-- The Chow class of the Gysin cycle of the zero cycle vanishes. -/
theorem gysin_zero :
    Hom.chowMk (zeroSchemeι L s ≫ f) δ k
        ⟨gysinCycle f δ k L s (0 : Function.locallyFinsupp (Points X) ℤ),
          gysinCycle_mem f δ k L s 0⟩ =
      0 :=
  sorry

/-- Taking the Chow class of the Gysin cycle preserves addition. -/
theorem gysin_add (α β : Hom.cycleGroup f δ (k + 1)) :
    Hom.chowMk (zeroSchemeι L s ≫ f) δ k
        ⟨gysinCycle f δ k L s
          ((α + β : Hom.cycleGroup f δ (k + 1)) :
            Function.locallyFinsupp (Points X) ℤ),
          gysinCycle_mem f δ k L s (α + β)⟩ =
      Hom.chowMk (zeroSchemeι L s ≫ f) δ k
          ⟨gysinCycle f δ k L s (α : Function.locallyFinsupp (Points X) ℤ),
            gysinCycle_mem f δ k L s α⟩ +
        Hom.chowMk (zeroSchemeι L s ≫ f) δ k
          ⟨gysinCycle f δ k L s (β : Function.locallyFinsupp (Points X) ℤ),
            gysinCycle_mem f δ k L s β⟩ :=
  sorry

/-- The refined Gysin homomorphism from degree-`k + 1` cycles on `X` to
degree-`k` Chow classes on the zero scheme `Z(s)`. -/
noncomputable def gysin :
    Hom.cycleGroup f δ (k + 1) →+ Hom.chowGroup (zeroSchemeι L s ≫ f) δ k :=
  (chowGysin δ f L s k).comp (QuotientAddGroup.mk' (RationalEquivalence.boundaries f δ (k + 1)))

/-- The Gysin homomorphism is computed by the explicit locally finite Gysin
cycle followed by the canonical map to `CH_k(Z(s))`. -/
theorem gysin_apply (α : Hom.cycleGroup f δ (k + 1)) :
    gysin f δ k L s α =
      Hom.chowMk (zeroSchemeι L s ≫ f) δ k
        ⟨gysinCycle f δ k L s (α : Function.locallyFinsupp (Points X) ℤ),
          gysinCycle_mem f δ k L s α⟩ :=
  rfl

/-- On a generator not contained in `Z(s)`, the Gysin homomorphism is the Chow
class of the associated cycle `[Z(s) ∩ closure({x})]_k`. -/
theorem gysin_point_of_not_mem (x : Points X)
    (hx : Hom.relativeDimensionFunction f δ x = k + 1)
    (hmem : x ∉ (zeroScheme L s).pointsSet) :
    gysin f δ k L s ⟨pointCycle x, pointCycle_mem f δ k x hx⟩ =
      Hom.chowMk (zeroSchemeι L s ≫ f) δ k
        ⟨gysinIntersectionCycle f δ k L s x,
          gysinIntersectionCycle_mem f δ k L s x⟩ := by
  change Hom.chowMk (zeroSchemeι L s ≫ f) δ k
    (gysinCycleHom δ f k L s _) = _
  congr 1
  apply Subtype.ext
  change gysinCycle f δ k L s (pointCycle x) = _
  rw [gysinCycle_pointCycle f δ k L s x hx]
  exact gysinGeneratorCycle_of_not_mem f δ k L s x hx hmem

/-- On a generator contained in `Z(s)`, the Gysin homomorphism is, for every
regular meromorphic section of `L` on `W = closure({x})`, the Chow class of
`i'_* div_L|_W(t)`. This is `i'_*(c1(L|_W) ∩ [W])`, and agrees with
`firstChernCapFundamental` on `W` when `dim_δ W = k + 1`. -/
theorem gysin_point_of_mem (x : Points X)
    (hx : Hom.relativeDimensionFunction f δ x = k + 1)
    (hmem : x ∈ (zeroScheme L s).pointsSet)
    (i' : PointClosure.space x ⟶ (zeroScheme L s).X)
    (hi' : i' ≫ zeroSchemeι L s = PointClosure.ι x)
    [IsClosedImmersion i']
    (t : meromorphicSections (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L))
    (ht : IsRegularMeromorphicSection (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L) t) :
    gysin f δ k L s ⟨pointCycle x, pointCycle_mem f δ k x hx⟩ =
      Hom.chowMk (zeroSchemeι L s ≫ f) δ k
        ⟨gysinContainedCycle f δ L s x i' t ht,
          gysinContainedCycle_mem f δ k L s x hx i' hi' t ht⟩ :=
  sorry

/-- Intersection with the effective Cartier divisor `Z(s)`, obtained by
pushforward of the Gysin class along `Z(s) ⟶ X`. -/
noncomputable def cartierIntersection [IsEffectiveCartierDivisor (zeroSchemeι L s)] :
    Hom.cycleGroup f δ (k + 1) →+ Hom.chowGroup f δ k :=
  (chowPushforward f δ (zeroScheme L s) k).comp (gysin f δ k L s)

/-- Effective-Cartier intersection is the pushforward of the Gysin class along
the zero-scheme immersion, i.e. `D · α = i_* (i* α)` in `CH_k(X)`. -/
theorem cartierIntersection_eq [IsEffectiveCartierDivisor (zeroSchemeι L s)]
    (α : Hom.cycleGroup f δ (k + 1)) :
    cartierIntersection f δ k L s α =
      chowPushforward f δ (zeroScheme L s) k (gysin f δ k L s α) :=
  rfl

/-- Cartier intersection sends the zero cycle to zero. -/
theorem cartierIntersection_zero [IsEffectiveCartierDivisor (zeroSchemeι L s)] :
    cartierIntersection f δ k L s 0 = 0 :=
  map_zero (cartierIntersection f δ k L s)

/-- Cartier intersection preserves addition. -/
theorem cartierIntersection_add [IsEffectiveCartierDivisor (zeroSchemeι L s)]
    (α β : Hom.cycleGroup f δ (k + 1)) :
    cartierIntersection f δ k L s (α + β) =
      cartierIntersection f δ k L s α + cartierIntersection f δ k L s β :=
  map_add (cartierIntersection f δ k L s) α β

end Hom

end AlgebraicGeometry.AlgebraicSpace
