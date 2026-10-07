module

public import stacks_project.Chap42.Lemma_42_44_1
public import stacks_project.Chap42.Lemma_42_44_2_VectorBundleMap
public import stacks_project.Chap42.«42_39_1_1_ChernClassTheory»
public import stacks_project.Chap42.Remark_42_38_11_TopChern
public import stacks_project.Chap42.Remark_42_35_5_Composition

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry
namespace ChowGroup
namespace AssociatedVectorBundle
namespace ShortExact

open Scheme.AssociatedVectorBundle

/-- The clopen locus on which the submodule and quotient in a short complex have ranks
`r₁` and `r₃`, respectively. -/
noncomputable def rankPairClopen {X : Scheme.{u}} (C : ShortComplex X.Modules)
    [C.X₁.IsFiniteLocallyFree] [C.X₃.IsFiniteLocallyFree] (r₁ r₃ : ℕ) : Clopens X :=
  Scheme.Modules.rankClopen C.X₁ r₁ ⊓ Scheme.Modules.rankClopen C.X₃ r₃

/-- Membership in `rankPairClopen` is the conjunction of the two indicated rank
conditions. -/
theorem mem_rankPairClopen {X : Scheme.{u}} (C : ShortComplex X.Modules)
    [C.X₁.IsFiniteLocallyFree] [C.X₃.IsFiniteLocallyFree]
    (r₁ r₃ : ℕ) (x : X) :
    x ∈ rankPairClopen C r₁ r₃ ↔
      C.X₁.fiberFinrank x = r₁ ∧ C.X₃.fiberFinrank x = r₃ := sorry

/-- The joint rank loci of the first and third terms cover the base scheme. -/
theorem rankPairClopen_iSup {X : Scheme.{u}} (C : ShortComplex X.Modules)
    [C.X₁.IsFiniteLocallyFree] [C.X₃.IsFiniteLocallyFree] :
    iSup (fun r : ℕ × ℕ ↦ (rankPairClopen C r.1 r.2).toOpens) = ⊤ := sorry

/-- A joint rank locus, regarded as a scheme over the original base. -/
noncomputable def rankPairOver {S : Scheme.{u}} (X : Over S)
    (C : ShortComplex X.left.Modules)
    [C.X₁.IsFiniteLocallyFree] [C.X₃.IsFiniteLocallyFree]
    (r₁ r₃ : ℕ) : Over S :=
  BivariantClass.OpenRestriction.over X (rankPairClopen C r₁ r₃).toOpens

/-- The structure map of `rankPairOver` is the open inclusion followed by `X.hom`. -/
theorem rankPairOver_hom {S : Scheme.{u}} (X : Over S)
    (C : ShortComplex X.left.Modules)
    [C.X₁.IsFiniteLocallyFree] [C.X₃.IsFiniteLocallyFree]
    (r₁ r₃ : ℕ) :
    (rankPairOver X C r₁ r₃).hom =
      Scheme.Opens.ι (rankPairClopen C r₁ r₃).toOpens ≫ X.hom := sorry

/-- A joint rank locus is locally of finite type over the ambient base. -/
instance rankPairOver_locallyOfFiniteType {S : Scheme.{u}} (X : Over S)
    [LocallyOfFiniteType X.hom] (C : ShortComplex X.left.Modules)
    [C.X₁.IsFiniteLocallyFree] [C.X₃.IsFiniteLocallyFree]
    (r₁ r₃ : ℕ) : LocallyOfFiniteType (rankPairOver X C r₁ r₃).hom := sorry

/-- The inclusion of a joint rank locus into the original `S`-scheme. -/
noncomputable def rankPairInclusion {S : Scheme.{u}} (X : Over S)
    (C : ShortComplex X.left.Modules)
    [C.X₁.IsFiniteLocallyFree] [C.X₃.IsFiniteLocallyFree]
    (r₁ r₃ : ℕ) : rankPairOver X C r₁ r₃ ⟶ X :=
  BivariantClass.OpenRestriction.ι X (rankPairClopen C r₁ r₃).toOpens

/-- The underlying map of `rankPairInclusion` is the canonical open immersion. -/
theorem rankPairInclusion_left {S : Scheme.{u}} (X : Over S)
    (C : ShortComplex X.left.Modules)
    [C.X₁.IsFiniteLocallyFree] [C.X₃.IsFiniteLocallyFree]
    (r₁ r₃ : ℕ) :
    (rankPairInclusion X C r₁ r₃).left =
      Scheme.Opens.ι (rankPairClopen C r₁ r₃).toOpens := sorry

/-- The joint-rank-locus inclusion is flat. -/
instance rankPairInclusion_flat {S : Scheme.{u}} (X : Over S)
    (C : ShortComplex X.left.Modules)
    [C.X₁.IsFiniteLocallyFree] [C.X₃.IsFiniteLocallyFree]
    (r₁ r₃ : ℕ) : Flat (rankPairInclusion X C r₁ r₃).left := sorry

/-- The joint-rank-locus inclusion has relative dimension zero. -/
instance rankPairInclusion_relativeDimension {S : Scheme.{u}} (X : Over S)
    (C : ShortComplex X.left.Modules)
    [C.X₁.IsFiniteLocallyFree] [C.X₃.IsFiniteLocallyFree]
    (r₁ r₃ : ℕ) :
    Scheme.Hom.RelativeDimension (rankPairInclusion X C r₁ r₃).left 0 := sorry

/-- Restriction of relative Chow classes to a joint rank locus. -/
noncomputable def rankPairPullback
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (C : ShortComplex X.left.Modules)
    [C.X₁.IsFiniteLocallyFree] [C.X₃.IsFiniteLocallyFree]
    (r₁ r₃ : ℕ) (k : ℤ) :
    RelativeChow δ X k →+ RelativeChow δ (rankPairOver X C r₁ r₃) k :=
  (BivariantClass.castRelativeDegree δ (add_zero k)).comp
    (ChowGroup.flatPullback δ (rankPairOver X C r₁ r₃) X
      (rankPairInclusion X C r₁ r₃) 0 k)

/-- `rankPairPullback` is flat pullback along the open inclusion followed by the
canonical degree-zero transport. -/
theorem rankPairPullback_def
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (C : ShortComplex X.left.Modules)
    [C.X₁.IsFiniteLocallyFree] [C.X₃.IsFiniteLocallyFree]
    (r₁ r₃ : ℕ) (k : ℤ) :
    rankPairPullback δ X C r₁ r₃ k =
      (BivariantClass.castRelativeDegree δ (add_zero k)).comp
        (ChowGroup.flatPullback δ (rankPairOver X C r₁ r₃) X
          (rankPairInclusion X C r₁ r₃) 0 k) := sorry

/-- Restriction of a short exact sequence to a joint rank locus. -/
noncomputable def rankPairRestriction {S : Scheme.{u}} (X : Over S)
    (C : ShortComplex X.left.Modules) (hC : C.ShortExact)
    [C.X₁.IsFiniteLocallyFree] [C.X₂.IsFiniteLocallyFree]
    [C.X₃.IsFiniteLocallyFree] (r₁ r₃ : ℕ) :
    ShortComplex (rankPairOver X C r₁ r₃).left.Modules :=
  C.map (Scheme.Modules.pullback (rankPairInclusion X C r₁ r₃).left)

/-- `rankPairRestriction` is termwise pullback along the joint-rank-locus inclusion. -/
theorem rankPairRestriction_def {S : Scheme.{u}} (X : Over S)
    (C : ShortComplex X.left.Modules) (hC : C.ShortExact)
    [C.X₁.IsFiniteLocallyFree] [C.X₂.IsFiniteLocallyFree]
    [C.X₃.IsFiniteLocallyFree] (r₁ r₃ : ℕ) :
    rankPairRestriction X C hC r₁ r₃ =
      C.map (Scheme.Modules.pullback (rankPairInclusion X C r₁ r₃).left) := sorry

/-- On a joint rank locus, the restricted first term has rank `r₁`. -/
instance rankPairRestriction_X₁_isFiniteLocallyFreeOfRank
    {S : Scheme.{u}} (X : Over S) (C : ShortComplex X.left.Modules)
    (hC : C.ShortExact) [C.X₁.IsFiniteLocallyFree] [C.X₂.IsFiniteLocallyFree]
    [C.X₃.IsFiniteLocallyFree] (r₁ r₃ : ℕ) :
    Scheme.Modules.IsFiniteLocallyFreeOfRank r₁
      (rankPairRestriction X C hC r₁ r₃).X₁ := sorry

/-- On a joint rank locus, the restricted quotient has rank `r₃`. -/
instance rankPairRestriction_X₃_isFiniteLocallyFreeOfRank
    {S : Scheme.{u}} (X : Over S) (C : ShortComplex X.left.Modules)
    (hC : C.ShortExact) [C.X₁.IsFiniteLocallyFree] [C.X₂.IsFiniteLocallyFree]
    [C.X₃.IsFiniteLocallyFree] (r₁ r₃ : ℕ) :
    Scheme.Modules.IsFiniteLocallyFreeOfRank r₃
      (rankPairRestriction X C hC r₁ r₃).X₃ := sorry

/-- Exactness makes the restricted middle term have rank `r₁ + r₃`. -/
instance rankPairRestriction_X₂_isFiniteLocallyFreeOfRank
    {S : Scheme.{u}} (X : Over S) (C : ShortComplex X.left.Modules)
    (hC : C.ShortExact) [C.X₁.IsFiniteLocallyFree] [C.X₂.IsFiniteLocallyFree]
    [C.X₃.IsFiniteLocallyFree] (r₁ r₃ : ℕ) :
    Scheme.Modules.IsFiniteLocallyFreeOfRank (r₁ + r₃)
      (rankPairRestriction X C hC r₁ r₃).X₂ := sorry

/-- Restriction to a joint rank locus preserves short exactness. -/
theorem rankPairRestriction_shortExact {S : Scheme.{u}} (X : Over S)
    (C : ShortComplex X.left.Modules) (hC : C.ShortExact)
    [C.X₁.IsFiniteLocallyFree] [C.X₂.IsFiniteLocallyFree]
    [C.X₃.IsFiniteLocallyFree] (r₁ r₃ : ℕ) :
    (rankPairRestriction X C hC r₁ r₃).ShortExact := sorry

/-- The rankwise top Chern components supplied by a Chern-class theory. -/
noncomputable def topChernComponents
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (classes : ChernClass.Theory δ X.hom)
    (E : X.left.Modules) [E.IsFiniteLocallyFree] (r : ℕ) :
    ChernClass.RankComponentClass δ X.hom E r r :=
  classes.baseComponent
    (BivariantClass.OpenRestriction.over X (Scheme.Modules.rankClopen E r).toOpens)
    ((Scheme.Modules.pullback
      (BivariantClass.OpenRestriction.ι X
        (Scheme.Modules.rankClopen E r).toOpens).left).obj E) r

/-- `topChernComponents` is the top homogeneous class on each rank locus. -/
theorem topChernComponents_def
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (classes : ChernClass.Theory δ X.hom)
    (E : X.left.Modules) [E.IsFiniteLocallyFree] (r : ℕ) :
    topChernComponents δ X classes E r =
      classes.baseComponent
        (BivariantClass.OpenRestriction.over X (Scheme.Modules.rankClopen E r).toOpens)
        ((Scheme.Modules.pullback
          (BivariantClass.OpenRestriction.ι X
            (Scheme.Modules.rankClopen E r).toOpens).left).obj E) r := sorry

/-- The joint rank locus lies in the rank-`r₃` locus of the quotient. -/
theorem rankPairClopen_le_thirdRank {S : Scheme.{u}} (X : Over S)
    (C : ShortComplex X.left.Modules)
    [C.X₁.IsFiniteLocallyFree] [C.X₃.IsFiniteLocallyFree]
    (r₁ r₃ : ℕ) :
    (rankPairClopen C r₁ r₃).toOpens ≤
      (𝟙 X : X ⟶ X).left ⁻¹ᵁ (Scheme.Modules.rankClopen C.X₃ r₃).toOpens := sorry

/-- A joint rank locus maps canonically to the rank-`r₃` locus of the quotient. -/
noncomputable def rankPairToThirdRankOver {S : Scheme.{u}} (X : Over S)
    (C : ShortComplex X.left.Modules)
    [C.X₁.IsFiniteLocallyFree] [C.X₃.IsFiniteLocallyFree]
    (r₁ r₃ : ℕ) : rankPairOver X C r₁ r₃ ⟶
      BivariantClass.OpenRestriction.over X
        (Scheme.Modules.rankClopen C.X₃ r₃).toOpens :=
  BivariantClass.OpenRestriction.hom (𝟙 X)
    (rankPairClopen C r₁ r₃).toOpens
    (Scheme.Modules.rankClopen C.X₃ r₃).toOpens
    (rankPairClopen_le_thirdRank X C r₁ r₃)

/-- The underlying map from a joint rank locus to the quotient-rank locus is the
corresponding restriction of the identity. -/
theorem rankPairToThirdRankOver_left {S : Scheme.{u}} (X : Over S)
    (C : ShortComplex X.left.Modules)
    [C.X₁.IsFiniteLocallyFree] [C.X₃.IsFiniteLocallyFree]
    (r₁ r₃ : ℕ) :
    (rankPairToThirdRankOver X C r₁ r₃).left =
      (𝟙 X : X ⟶ X).left.resLE
        (Scheme.Modules.rankClopen C.X₃ r₃).toOpens
        (rankPairClopen C r₁ r₃).toOpens
        (rankPairClopen_le_thirdRank X C r₁ r₃) := sorry

/-- The top Chern class on a joint rank locus, obtained by restricting the corresponding
component of `ChernClass.topOfRankComponents`. -/
noncomputable def rankPairTopChern
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (classes : ChernClass.Theory δ X.hom)
    (C : ShortComplex X.left.Modules)
    [C.X₁.IsFiniteLocallyFree] [C.X₃.IsFiniteLocallyFree] (r₁ r₃ : ℕ) :
    ChowCohomology.Nonnegative.degree δ (rankPairOver X C r₁ r₃).hom r₃ :=
  ChernClass.restrictComponent δ (rankPairToThirdRankOver X C r₁ r₃) r₃
    (DirectSum.component ℤ ℕ (ChernClass.RankComponentClass δ X.hom C.X₃ r₃) r₃
      (ChernClass.topOfRankComponents δ X.hom C.X₃
        (topChernComponents δ X classes C.X₃) r₃))

/-- `rankPairTopChern` is the restriction of the rankwise assembled top Chern class. -/
theorem rankPairTopChern_def
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (classes : ChernClass.Theory δ X.hom)
    (C : ShortComplex X.left.Modules)
    [C.X₁.IsFiniteLocallyFree] [C.X₃.IsFiniteLocallyFree] (r₁ r₃ : ℕ) :
    rankPairTopChern δ X classes C r₁ r₃ =
      ChernClass.restrictComponent δ (rankPairToThirdRankOver X C r₁ r₃) r₃
        (DirectSum.component ℤ ℕ
          (ChernClass.RankComponentClass δ X.hom C.X₃ r₃) r₃
          (ChernClass.topOfRankComponents δ X.hom C.X₃
            (topChernComponents δ X classes C.X₃) r₃)) := sorry

/-- The grading identity comparing pullback after a rank-`r₃` top Chern cap with the
degree of the rank-`r₁` subbundle. -/
theorem topChernPullbackDegree (k : ℤ) (r₁ r₃ : ℕ) :
    (k - (r₃ : ℤ)) + ((r₁ + r₃ : ℕ) : ℤ) = k + (r₁ : ℤ) := sorry

/-- The fixed-rank component of the short-exact-sequence pushforward formula. -/
theorem pushforward_pullback_eq_topChern_of_rank
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (classes : ChernClass.Theory δ X.hom) (C : ShortComplex X.left.Modules)
    (hC : C.ShortExact) (r₁ r₃ : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r₁ C.X₁]
    [Scheme.Modules.IsFiniteLocallyFreeOfRank (r₁ + r₃) C.X₂]
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r₃ C.X₃]
    (P₁ : Scheme.RelativeSpectrumOver
      (Scheme.SymmetricAlgebra.qcAlgebra (Scheme.Modules.dual C.X₁)))
    [Scheme.IsRelativeSpectrumOver P₁]
    (P₂ : Scheme.RelativeSpectrumOver
      (Scheme.SymmetricAlgebra.qcAlgebra (Scheme.Modules.dual C.X₂)))
    [Scheme.IsRelativeSpectrumOver P₂]
    (k : ℤ) (α : RelativeChow δ X k) :
    pushforward δ X C hC r₁ r₃ P₁ P₂ (k + (r₁ : ℤ))
        (ChowGroup.flatPullback δ
          (over X (Scheme.Modules.dual C.X₁) P₁) X
          (projectionOver X (Scheme.Modules.dual C.X₁) P₁) r₁ k α) =
      BivariantClass.castRelativeDegree δ (topChernPullbackDegree k r₁ r₃)
        (ChowGroup.flatPullback δ
          (over X (Scheme.Modules.dual C.X₂) P₂) X
          (projectionOver X (Scheme.Modules.dual C.X₂) P₂) (r₁ + r₃)
          (k - (r₃ : ℤ))
          ((classes.component C.X₃ r₃).cap
            (𝟙 X) (𝟙 X) (𝟙 X) IsPullback.of_id_snd k α)) := sorry

/-- Lemma 42.44.2: for a short exact sequence `0 ⟶ C.X₁ ⟶ C.X₂ ⟶ C.X₃ ⟶ 0`
of finite locally free modules, the pushforward/pullback identity holds on every joint
rank locus. These clopen loci cover `X`, and the top Chern terms are the restrictions of
the class assembled by `ChernClass.topOfRankComponents`. -/
@[stacks 0FAA]
theorem pushforward_pullback_eq_topChern
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (classes : ChernClass.Theory δ X.hom) (C : ShortComplex X.left.Modules)
    [C.X₁.IsFiniteLocallyFree] [C.X₂.IsFiniteLocallyFree]
    [C.X₃.IsFiniteLocallyFree] (hC : C.ShortExact) (r₁ r₃ : ℕ)
    (P₁ : Scheme.RelativeSpectrumOver
      (Scheme.SymmetricAlgebra.qcAlgebra
        (Scheme.Modules.dual (rankPairRestriction X C hC r₁ r₃).X₁)))
    [Scheme.IsRelativeSpectrumOver P₁]
    (P₂ : Scheme.RelativeSpectrumOver
      (Scheme.SymmetricAlgebra.qcAlgebra
        (Scheme.Modules.dual (rankPairRestriction X C hC r₁ r₃).X₂)))
    [Scheme.IsRelativeSpectrumOver P₂]
    (k : ℤ) (α : RelativeChow δ X k) :
    pushforward δ (rankPairOver X C r₁ r₃) (rankPairRestriction X C hC r₁ r₃)
        (rankPairRestriction_shortExact X C hC r₁ r₃) r₁ r₃ P₁ P₂
        (k + (r₁ : ℤ))
        (ChowGroup.flatPullback δ
          (over (rankPairOver X C r₁ r₃)
            (Scheme.Modules.dual (rankPairRestriction X C hC r₁ r₃).X₁) P₁)
          (rankPairOver X C r₁ r₃)
          (projectionOver (rankPairOver X C r₁ r₃)
            (Scheme.Modules.dual (rankPairRestriction X C hC r₁ r₃).X₁) P₁)
          r₁ k
          (rankPairPullback δ X C r₁ r₃ k α)) =
      BivariantClass.castRelativeDegree δ (topChernPullbackDegree k r₁ r₃)
        (ChowGroup.flatPullback δ
          (over (rankPairOver X C r₁ r₃)
            (Scheme.Modules.dual (rankPairRestriction X C hC r₁ r₃).X₂) P₂)
          (rankPairOver X C r₁ r₃)
          (projectionOver (rankPairOver X C r₁ r₃)
            (Scheme.Modules.dual (rankPairRestriction X C hC r₁ r₃).X₂) P₂)
          (r₁ + r₃) (k - (r₃ : ℤ))
          ((rankPairTopChern δ X classes C r₁ r₃).cap
            (𝟙 (rankPairOver X C r₁ r₃)) (𝟙 (rankPairOver X C r₁ r₃))
            (𝟙 (rankPairOver X C r₁ r₃)) IsPullback.of_id_snd k
            (rankPairPullback δ X C r₁ r₃ k α))) := sorry

end ShortExact
end AssociatedVectorBundle
end ChowGroup
end AlgebraicGeometry
