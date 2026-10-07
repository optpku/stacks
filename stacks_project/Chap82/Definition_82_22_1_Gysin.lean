module

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

/-- The zero scheme of a section remains quasi-separated over the fixed good
base. -/
instance instQuasiSeparated_zeroScheme_comp (L : X.Modules) [isInvertibleObject L]
    (s : L.sections) : QuasiSeparated (zeroSchemeι L s ≫ f) :=
  sorry

/-- The zero scheme of a section remains locally of finite type over the fixed
good base. -/
instance instLocallyOfFiniteType_zeroScheme_comp (L : X.Modules)
    [isInvertibleObject L] (s : L.sections) :
    LocallyOfFiniteType (zeroSchemeι L s ≫ f) :=
  sorry

/-- The reduced closure of a point is locally Noetherian. -/
instance instIsLocallyNoetherian_pointClosure_space (x : Points X) :
    IsLocallyNoetherian (PointClosure.space x) :=
  sorry

/-- The reduced closure of a point is quasi-separated. -/
instance instIsQuasiSeparated_pointClosure_space (x : Points X) :
    IsQuasiSeparated (PointClosure.space x) :=
  sorry

/-- The reduced closure of a point is decent. -/
instance instIsDecent_pointClosure_space (x : Points X) :
    IsDecent (PointClosure.space x) :=
  instIsDecent_of_isQuasiSeparated (PointClosure.space x)

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

variable (k : ℤ)

/-- The generator cycle of an integral closed subspace of relative dimension
`k + 1`. -/
noncomputable def pointCycle (x : Points X) :
    Function.locallyFinsupp (Points X) ℤ :=
  @Function.locallyFinsuppWithin.single (Points X) _ ℤ (Classical.decEq _) _ x 1

/-- The generator cycle of a point of relative dimension `k + 1` is a
`(k + 1)`-cycle. -/
theorem pointCycle_mem (x : Points X)
    (hx : f.relativeDimensionFunction δ x = k + 1) :
    pointCycle x ∈ f.cycleGroup δ (k + 1) :=
  sorry

variable (L : X.Modules) [isInvertibleObject L] (s : L.sections)

/-- A point of `Z(s)` has an induced closed immersion from its reduced closure
in `X` into `Z(s)`, factoring the canonical immersion into `X`. -/
theorem exists_gysinContainedImmersion (x : Points X)
    (hx : x ∈ (zeroScheme L s).pointsSet) :
    ∃ i' : PointClosure.space x ⟶ (zeroScheme L s).X,
      i' ≫ zeroSchemeι L s = PointClosure.ι x ∧ IsClosedImmersion i' :=
  sorry

/-- The induced closed immersion `i' : closure({x}) ⟶ Z(s)` of a point contained
in the zero scheme. -/
noncomputable def gysinContainedImmersion (x : Points X)
    (hx : x ∈ (zeroScheme L s).pointsSet) :
    PointClosure.space x ⟶ (zeroScheme L s).X :=
  Classical.choose (exists_gysinContainedImmersion L s x hx)

/-- The induced immersion into `Z(s)` factors the reduced point-closure
immersion. -/
theorem gysinContainedImmersion_comp (x : Points X)
    (hx : x ∈ (zeroScheme L s).pointsSet) :
    gysinContainedImmersion L s x hx ≫ zeroSchemeι L s = PointClosure.ι x :=
  sorry

/-- The induced map from a contained reduced point closure to `Z(s)` is a closed
immersion. -/
instance instIsClosedImmersion_gysinContainedImmersion (x : Points X)
    (hx : x ∈ (zeroScheme L s).pointsSet) :
    IsClosedImmersion (gysinContainedImmersion L s x hx) :=
  (Classical.choose_spec (exists_gysinContainedImmersion L s x hx)).2

/-- The restriction of an invertible module to a reduced point closure has a
regular meromorphic section. -/
theorem exists_regularMeromorphicSection_pointClosure (x : Points X) :
    ∃ t : meromorphicSections (PointClosure.space x)
        ((Modules.pullback (PointClosure.ι x)).obj L),
      IsRegularMeromorphicSection (PointClosure.space x)
        ((Modules.pullback (PointClosure.ι x)).obj L) t :=
  sorry

/-- A chosen regular meromorphic section of `L` on the reduced closure of `x`. -/
noncomputable def gysinContainedSection (x : Points X) :
    meromorphicSections (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L) :=
  Classical.choose (exists_regularMeromorphicSection_pointClosure L x)

/-- The chosen meromorphic section on a reduced point closure is regular. -/
theorem gysinContainedSection_isRegular (x : Points X) :
    IsRegularMeromorphicSection (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L)
      (gysinContainedSection L x) :=
  sorry

/-- The divisor cycle of a regular meromorphic section of the restriction of `L`
to the reduced closure of `x`. -/
noncomputable def meromorphicSectionDivisorCycle_pointClosure (x : Points X)
    (t : meromorphicSections (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L))
    (ht : IsRegularMeromorphicSection (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L) t) :
    Function.locallyFinsupp (Points (PointClosure.space x)) ℤ :=
  @meromorphicSectionDivisorCycle S B (PointClosure.space x)
    inferInstance inferInstance (PointClosure.ι x ≫ f)
    inferInstance inferInstance δ inferInstance inferInstance
    ((Modules.pullback (PointClosure.ι x)).obj L)
    (Modules.isInvertibleObject_map_pullback (PointClosure.ι x) L) t ht

/-- The divisor cycle of a regular meromorphic section on a reduced point
closure of relative dimension `k + 1` is a `k`-cycle. -/
theorem meromorphicSectionDivisorCycle_pointClosure_mem (x : Points X)
    (hx : f.relativeDimensionFunction δ x = k + 1)
    (t : meromorphicSections (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L))
    (ht : IsRegularMeromorphicSection (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L) t) :
    meromorphicSectionDivisorCycle_pointClosure f δ L x t ht ∈
      (PointClosure.ι x ≫ f).cycleGroup δ k :=
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
    (hx : f.relativeDimensionFunction δ x = k + 1)
    (i' : PointClosure.space x ⟶ (zeroScheme L s).X) [IsClosedImmersion i']
    (hi' : i' ≫ zeroSchemeι L s = PointClosure.ι x)
    (t : meromorphicSections (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L))
    (ht : IsRegularMeromorphicSection (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L) t) :
    gysinContainedCycle f δ L s x i' t ht ∈
      (zeroSchemeι L s ≫ f).cycleGroup δ k :=
  sorry

/-- The cycle on `Z(s)` contributed by a degree-`k + 1` point of `X`. Off the
zero scheme this is the associated cycle of `Z(s) ∩ closure({x})`; on the zero
scheme it is the pushforward along the induced closed immersion of a regular
meromorphic-section divisor cycle of `L` on that point closure. -/
noncomputable def gysinGeneratorCycle (x : Points X)
    (hx : f.relativeDimensionFunction δ x = k + 1) :
    Function.locallyFinsupp (Points (zeroScheme L s).X) ℤ :=
  let _ := hx
  @dite (Function.locallyFinsupp (Points (zeroScheme L s).X) ℤ)
    (x ∈ (zeroScheme L s).pointsSet) (Classical.propDecidable _)
    (fun hmem ↦
      gysinContainedCycle f δ L s x (gysinContainedImmersion L s x hmem)
        (gysinContainedSection L x) (gysinContainedSection_isRegular L x))
    (fun _ ↦ gysinIntersectionCycle f δ k L s x)

/-- Off `Z(s)`, the Gysin generator is the associated cycle of
`Z(s) ∩ closure({x})`. -/
theorem gysinGeneratorCycle_of_not_mem (x : Points X)
    (hx : f.relativeDimensionFunction δ x = k + 1)
    (hmem : x ∉ (zeroScheme L s).pointsSet) :
    gysinGeneratorCycle f δ k L s x hx = gysinIntersectionCycle f δ k L s x :=
  sorry

/-- On `Z(s)`, the Gysin generator is the pushforward of the chosen regular
meromorphic-section divisor cycle along the induced closed immersion into
`Z(s)`. -/
theorem gysinGeneratorCycle_of_mem (x : Points X)
    (hx : f.relativeDimensionFunction δ x = k + 1)
    (hmem : x ∈ (zeroScheme L s).pointsSet) :
    gysinGeneratorCycle f δ k L s x hx =
      gysinContainedCycle f δ L s x (gysinContainedImmersion L s x hmem)
        (gysinContainedSection L x) (gysinContainedSection_isRegular L x) :=
  sorry

/-- The coefficient-weighted Gysin generator cycles of a degree-`k + 1` cycle
form a locally finite family on `Z(s)`. -/
theorem gysinGeneratorTermsLocallyFinite
    (α : Function.locallyFinsupp (Points X) ℤ) :
    LocallyFinite fun x : Points X ↦
      (if hx : f.relativeDimensionFunction δ x = k + 1 then
        α x • gysinGeneratorCycle f δ k L s x hx
      else 0).support :=
  sorry

/-- The explicit locally finite cycle on `Z(s)` obtained by extending the two
generator rules linearly. -/
noncomputable def gysinCycle (α : Function.locallyFinsupp (Points X) ℤ) :
    Function.locallyFinsupp (Points (zeroScheme L s).X) ℤ :=
  AlgebraicCycle.locallyFiniteSum
    (fun x : Points X ↦
      if hx : f.relativeDimensionFunction δ x = k + 1 then
        α x • gysinGeneratorCycle f δ k L s x hx
      else 0)
    (gysinGeneratorTermsLocallyFinite f δ k L s α)

/-- Coefficients of the Gysin cycle are the pointwise finite sums of the
weighted generator cycles. -/
theorem gysinCycle_apply (α : Function.locallyFinsupp (Points X) ℤ)
    (z : Points (zeroScheme L s).X) :
    gysinCycle f δ k L s α z =
      ∑ᶠ x : Points X,
        (if hx : f.relativeDimensionFunction δ x = k + 1 then
          α x • gysinGeneratorCycle f δ k L s x hx
        else 0) z :=
  sorry

/-- The Gysin cycle of a `(k + 1)`-cycle is a `k`-cycle on `Z(s)`. -/
theorem gysinCycle_mem (α : f.cycleGroup δ (k + 1)) :
    gysinCycle f δ k L s (α : Function.locallyFinsupp (Points X) ℤ) ∈
      (zeroSchemeι L s ≫ f).cycleGroup δ k :=
  sorry

/-- The Chow class of the Gysin cycle of the zero cycle vanishes. -/
theorem gysin_zero :
    (zeroSchemeι L s ≫ f).chowMk δ k
        ⟨gysinCycle f δ k L s (0 : Function.locallyFinsupp (Points X) ℤ),
          gysinCycle_mem f δ k L s 0⟩ =
      0 :=
  sorry

/-- Taking the Chow class of the Gysin cycle preserves addition. -/
theorem gysin_add (α β : f.cycleGroup δ (k + 1)) :
    (zeroSchemeι L s ≫ f).chowMk δ k
        ⟨gysinCycle f δ k L s
          ((α + β : f.cycleGroup δ (k + 1)) :
            Function.locallyFinsupp (Points X) ℤ),
          gysinCycle_mem f δ k L s (α + β)⟩ =
      (zeroSchemeι L s ≫ f).chowMk δ k
          ⟨gysinCycle f δ k L s (α : Function.locallyFinsupp (Points X) ℤ),
            gysinCycle_mem f δ k L s α⟩ +
        (zeroSchemeι L s ≫ f).chowMk δ k
          ⟨gysinCycle f δ k L s (β : Function.locallyFinsupp (Points X) ℤ),
            gysinCycle_mem f δ k L s β⟩ :=
  sorry

/-- The refined Gysin homomorphism from degree-`k + 1` cycles on `X` to
degree-`k` Chow classes on the zero scheme `Z(s)`. -/
noncomputable def gysin :
    f.cycleGroup δ (k + 1) →+ (zeroSchemeι L s ≫ f).chowGroup δ k where
  toFun := fun α ↦
    (zeroSchemeι L s ≫ f).chowMk δ k
      ⟨gysinCycle f δ k L s (α : Function.locallyFinsupp (Points X) ℤ),
        gysinCycle_mem f δ k L s α⟩
  map_zero' := gysin_zero f δ k L s
  map_add' := gysin_add f δ k L s

/-- The Gysin homomorphism is computed by the explicit locally finite Gysin
cycle followed by the canonical map to `CH_k(Z(s))`. -/
theorem gysin_apply (α : f.cycleGroup δ (k + 1)) :
    gysin f δ k L s α =
      (zeroSchemeι L s ≫ f).chowMk δ k
        ⟨gysinCycle f δ k L s (α : Function.locallyFinsupp (Points X) ℤ),
          gysinCycle_mem f δ k L s α⟩ :=
  sorry

/-- On a generator not contained in `Z(s)`, the Gysin homomorphism is the Chow
class of the associated cycle `[Z(s) ∩ closure({x})]_k`. -/
theorem gysin_point_of_not_mem (x : Points X)
    (hx : f.relativeDimensionFunction δ x = k + 1)
    (hmem : x ∉ (zeroScheme L s).pointsSet) :
    gysin f δ k L s ⟨pointCycle x, pointCycle_mem f δ k x hx⟩ =
      (zeroSchemeι L s ≫ f).chowMk δ k
        ⟨gysinIntersectionCycle f δ k L s x,
          gysinIntersectionCycle_mem f δ k L s x⟩ :=
  sorry

/-- On a generator contained in `Z(s)`, the Gysin homomorphism is, for every
regular meromorphic section of `L` on `W = closure({x})`, the Chow class of
`i'_* div_L|_W(t)`. This is `i'_*(c1(L|_W) ∩ [W])`, and agrees with
`firstChernCapFundamental` on `W` when `dim_δ W = k + 1`. -/
theorem gysin_point_of_mem (x : Points X)
    (hx : f.relativeDimensionFunction δ x = k + 1)
    (hmem : x ∈ (zeroScheme L s).pointsSet)
    (i' : PointClosure.space x ⟶ (zeroScheme L s).X)
    (hi' : i' ≫ zeroSchemeι L s = PointClosure.ι x)
    [IsClosedImmersion i']
    (t : meromorphicSections (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L))
    (ht : IsRegularMeromorphicSection (PointClosure.space x)
      ((Modules.pullback (PointClosure.ι x)).obj L) t) :
    gysin f δ k L s ⟨pointCycle x, pointCycle_mem f δ k x hx⟩ =
      (zeroSchemeι L s ≫ f).chowMk δ k
        ⟨gysinContainedCycle f δ L s x i' t ht,
          gysinContainedCycle_mem f δ k L s x hx i' hi' t ht⟩ :=
  sorry

/-- Intersection with the effective Cartier divisor `Z(s)`, obtained by
pushforward of the Gysin class along `Z(s) ⟶ X`. -/
noncomputable def cartierIntersection [IsEffectiveCartierDivisor (zeroSchemeι L s)] :
    f.cycleGroup δ (k + 1) →+ f.chowGroup δ k :=
  (chowPushforward f δ (zeroScheme L s) k).comp (gysin f δ k L s)

/-- Effective-Cartier intersection is the pushforward of the Gysin class along
the zero-scheme immersion, i.e. `D · α = i_* (i* α)` in `CH_k(X)`. -/
theorem cartierIntersection_eq [IsEffectiveCartierDivisor (zeroSchemeι L s)]
    (α : f.cycleGroup δ (k + 1)) :
    cartierIntersection f δ k L s α =
      chowPushforward f δ (zeroScheme L s) k (gysin f δ k L s α) :=
  sorry

/-- Cartier intersection sends the zero cycle to zero. -/
theorem cartierIntersection_zero [IsEffectiveCartierDivisor (zeroSchemeι L s)] :
    cartierIntersection f δ k L s 0 = 0 :=
  sorry

/-- Cartier intersection preserves addition. -/
theorem cartierIntersection_add [IsEffectiveCartierDivisor (zeroSchemeι L s)]
    (α β : f.cycleGroup δ (k + 1)) :
    cartierIntersection f δ k L s (α + β) =
      cartierIntersection f δ k L s α + cartierIntersection f δ k L s β :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
