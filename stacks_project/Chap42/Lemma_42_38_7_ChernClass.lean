module

public import stacks_project.Chap42.Lemma_42_35_1
public import stacks_project.Chap42.Definition_42_38_1_ChernCap
public import stacks_project.Chap42.Lemma_42_38_3
public import stacks_project.Chap42.Lemma_42_38_4
public import stacks_project.Chap42.Lemma_42_38_5
public import stacks_project.Chap42.Lemma_42_38_6
public import stacks_project.Chap42.Remark_42_34_2_Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.ChernClassCap

/-- The intrinsic Chern-class cap characterized by the projective-bundle relation. -/
noncomputable def canonical
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (k : ℤ)
    (α : CycleGroup X (p.relativeDimensionFunction δ) k) :
    ChernClassCap δ p E r k α :=
  Classical.choice (nonempty δ p E r k α)

/-- The intrinsic characterization makes `canonical` equal to every realization. -/
theorem canonical_eq
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (k : ℤ)
    (α : CycleGroup X (p.relativeDimensionFunction δ) k)
    (c : ChernClassCap δ p E r k α) : canonical δ p E r k α = c := sorry

/-- The zeroth component of `canonical` is the Chow class of the input cycle. -/
theorem canonical_component_zero
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (k : ℤ)
    (α : CycleGroup X (p.relativeDimensionFunction δ) k) :
    (canonical δ p E r k α).component 0 =
      @reindex X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k (k - (0 : ℕ))
        (sub_zero k).symm
        (@chowClass X (LocallyOfFiniteType.isLocallyNoetherian p)
          (p.relativeDimensionFunction δ) inferInstance k α) := sorry

/-- Components of `canonical` above the rank vanish. -/
theorem canonical_component_eq_zero
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (k : ℤ)
    (α : CycleGroup X (p.relativeDimensionFunction δ) k) (j : ℕ) (hj : r < j) :
    (canonical δ p E r k α).component j = 0 := sorry

/-- The selected intrinsic component sends the zero cycle to zero. -/
theorem canonical_component_zero_cycle
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (k : ℤ) (i : Fin (r + 1)) :
    (canonical δ p E r k 0).component (i : ℕ) = 0 := sorry

/-- The selected intrinsic component is additive in the input cycle. -/
theorem canonical_component_add
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (k : ℤ) (i : Fin (r + 1))
    (α β : CycleGroup X (p.relativeDimensionFunction δ) k) :
    (canonical δ p E r k (α + β)).component (i : ℕ) =
      (canonical δ p E r k α).component (i : ℕ) +
        (canonical δ p E r k β).component (i : ℕ) := sorry

/-- The cycle-level additive homomorphism given by the `i`th intrinsic Chern-class cap. -/
noncomputable def componentHom
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [hE : Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (k : ℤ) (i : Fin (r + 1)) :
    CycleGroup X (p.relativeDimensionFunction δ) k →+
      @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance (k - (i : ℕ)) :=
  { toFun := fun α ↦ (canonical δ p E r k α).component (i : ℕ)
    map_zero' := canonical_component_zero_cycle δ p E r k i
    map_add' := canonical_component_add δ p E r k i }

/-- Evaluation of `componentHom` is the corresponding intrinsic canonical component. -/
theorem componentHom_apply
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [hE : Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (k : ℤ) (i : Fin (r + 1))
    (α : CycleGroup X (p.relativeDimensionFunction δ) k) :
    componentHom δ p E r k i α =
      (canonical δ p E r k α).component (i : ℕ) := sorry

/-- The complete family of concrete cycle-level component maps satisfies the
projective-bundle characterization. -/
theorem componentHom_isChernClassCap
    {S X P : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [hE : Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E) (k : ℤ) :
    ProjectiveBundle.IsChernClassCap δ p E r π hπ k (componentHom δ p E r k) := sorry

/-- Rational-equivalence boundaries lie in the kernel of every concrete
cycle-level Chern component. -/
theorem componentHom_boundaries_le_ker
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [hE : Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (k : ℤ) (i : Fin (r + 1)) :
    @RationalEquivalence.boundaries X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k ≤
      (componentHom δ p E r k i).ker := sorry

end AlgebraicGeometry.ChowGroup.ChernClassCap

namespace AlgebraicGeometry.ChowGroup

/-- Intersection with the `i`th Chern class of a finite locally free module on
relative Chow groups. -/
noncomputable def chernClassCap
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [hE : Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (i : Fin (r + 1)) (k : ℤ) :
    @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k →+
      @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance (k - (i : ℕ)) :=
  QuotientAddGroup.lift
    (@RationalEquivalence.boundaries X (LocallyOfFiniteType.isLocallyNoetherian p)
      (p.relativeDimensionFunction δ) inferInstance k)
    (ChernClassCap.componentHom δ p E r k i)
    (ChernClassCap.componentHom_boundaries_le_ker δ p E r k i)

/-- The Chow-level Chern cap on a cycle class is the corresponding intrinsic
cycle-level component. -/
theorem chernClassCap_chowClass
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [hE : Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (i : Fin (r + 1)) (k : ℤ)
    (α : CycleGroup X (p.relativeDimensionFunction δ) k) :
    chernClassCap δ p E r i k
        (@chowClass X (LocallyOfFiniteType.isLocallyNoetherian p)
          (p.relativeDimensionFunction δ) inferInstance k α) =
      (ChernClassCap.canonical δ p E r k α).component (i : ℕ) := sorry

end AlgebraicGeometry.ChowGroup

namespace AlgebraicGeometry.ChernClass

variable {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ)
variable [IsDimensionFunction δ] (p : X ⟶ S) [LocallyOfFiniteType p]

variable (E : X.Modules) (r : ℕ)
variable [hE : Scheme.Modules.IsFiniteLocallyFreeOfRank r E]

/-- The cap family obtained by intersecting with the selected Chern component of
the pulled-back finite locally free module. -/
noncomputable def cap (i : Fin (r + 1)) :
    BivariantClass.CapFamily δ (𝟙 (Over.mk p)) (i : ℤ) :=
  fun {X' _} _ _ f _ g _ square k ↦
    (@ChowGroup.chernClassCap S X'.left inferInstance δ inferInstance
      X'.hom inferInstance ((Scheme.Modules.pullback f.left).obj E) r
      (@Scheme.Modules.pullback_isFiniteLocallyFreeOfRank X'.left X f.left E r hE)
      i k).comp
        ((ChowCohomology.castDegree δ (Int.sub_zero k)).comp
          (ChowCohomology.identityCap δ p f _ g square k))

/-- Evaluation of `cap` is Chern intersection after transport across the displayed
identity pullback square. -/
theorem cap_apply (i : Fin (r + 1))
    {X' Y' : Over S} [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (f : X' ⟶ Over.mk p) (f' : X' ⟶ Y') (g : Y' ⟶ Over.mk p)
    [LocallyOfFiniteType g.left]
    (square : IsPullback f.left f'.left (𝟙 X) g.left) (k : ℤ) :
    cap δ p E r i f f' g square k =
      (@ChowGroup.chernClassCap S X'.left inferInstance δ inferInstance
        X'.hom inferInstance ((Scheme.Modules.pullback f.left).obj E) r
        (@Scheme.Modules.pullback_isFiniteLocallyFreeOfRank X'.left X f.left E r hE)
        i k).comp
          ((ChowCohomology.castDegree δ (Int.sub_zero k)).comp
            (ChowCohomology.identityCap δ p f f' g square k)) := sorry

/-- Chern-component intersection commutes with proper pushforward. -/
theorem capMapProper (i : Fin (r + 1)) :
    BivariantClass.CompatibleWithProperPushforward δ (cap δ p E r i) := sorry

/-- Chern-component intersection commutes with flat pullback. -/
theorem capPullbackFlat (i : Fin (r + 1)) :
    BivariantClass.CompatibleWithFlatPullback δ (cap δ p E r i) := sorry

/-- Chern-component intersection commutes with effective-Cartier Gysin pullback. -/
theorem capGysinCartier (i : Fin (r + 1)) :
    BivariantClass.CompatibleWithCartierGysin δ (cap δ p E r i) := sorry

/-- The degree-`i` Chow-cohomology class defined by the `i`th Chern class of a
finite locally free module of rank `r`. -/
noncomputable def component (i : Fin (r + 1)) :
    ChowCohomology.degree δ p (i : ℤ) where
  cap := cap δ p E r i
  map_proper := capMapProper δ p E r i
  pullback_flat := capPullbackFlat δ p E r i
  gysin_cartier := capGysinCartier δ p E r i

/-- The cap family of `component` is the canonical Chern-component cap family. -/
theorem component_cap (i : Fin (r + 1))
    {X' Y' : Over S} [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (f : X' ⟶ Over.mk p) (f' : X' ⟶ Y') (g : Y' ⟶ Over.mk p)
    [LocallyOfFiniteType g.left]
    (square : IsPullback f.left f'.left (𝟙 X) g.left) (k : ℤ) :
    (component δ p E r i).cap f f' g square k =
      cap δ p E r i f f' g square k := sorry

/-- On the canonical identity square, `component` acts by intersection with the
`i`th Chern class of the pulled-back module. -/
theorem component_apply (i : Fin (r + 1))
    {X' : Over S} [LocallyOfFiniteType X'.hom] (f : X' ⟶ Over.mk p)
    (k : ℤ) (α : RelativeChow δ X' k) :
    (component δ p E r i).cap f (𝟙 X') f IsPullback.of_id_snd k α =
      @ChowGroup.chernClassCap S X'.left inferInstance δ inferInstance
        X'.hom inferInstance ((Scheme.Modules.pullback f.left).obj E) r
        (@Scheme.Modules.pullback_isFiniteLocallyFreeOfRank X'.left X f.left E r hE)
        i k α := sorry

end AlgebraicGeometry.ChernClass
