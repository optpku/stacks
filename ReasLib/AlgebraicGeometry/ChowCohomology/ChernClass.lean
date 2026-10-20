/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveBundle.ChernClassCap.FlatPullback
public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveBundle.ChernClassCap.Gysin
public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveBundle.ChernClassCap.Pushforward
public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveBundle.ChernClassCap.RationalEquivalence
public import ReasLib.AlgebraicGeometry.ChowCohomology
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ChowCohomology.ChernClass

/-- The canonical intrinsic Chern-class cap determined by the projective-bundle
relation. -/
noncomputable def canonicalCap
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (k : ℤ)
    (α : CycleGroup X (p.relativeDimensionFunction δ) k) :
    ChowGroup.ChernClassCap δ p E r k α :=
  Classical.choice (ChowGroup.ChernClassCap.nonempty δ p E r k α)

/-- The intrinsic characterization identifies the canonical Chern-class cap
with every realization of that characterization. -/
theorem canonicalCap_eq
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (k : ℤ)
    (α : CycleGroup X (p.relativeDimensionFunction δ) k)
    (c : ChowGroup.ChernClassCap δ p E r k α) :
    canonicalCap δ p E r k α = c := sorry

/-- The zeroth component of the canonical Chern-class cap is the Chow class of
the input cycle. -/
theorem canonicalCap_component_zero
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (k : ℤ)
    (α : CycleGroup X (p.relativeDimensionFunction δ) k) :
    (canonicalCap δ p E r k α).component 0 =
      @ChowGroup.reindex X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k (k - (0 : ℕ))
        (sub_zero k).symm
        (@chowClass X (LocallyOfFiniteType.isLocallyNoetherian p)
          (p.relativeDimensionFunction δ) inferInstance k α) := sorry

/-- Every component of the canonical Chern-class cap above the rank vanishes. -/
theorem canonicalCap_component_eq_zero
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (k : ℤ)
    (α : CycleGroup X (p.relativeDimensionFunction δ) k) (j : ℕ) (hj : r < j) :
    (canonicalCap δ p E r k α).component j = 0 := sorry

/-- Every component of the canonical Chern-class cap sends the zero cycle to
zero. -/
theorem canonicalCap_component_zero_cycle
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (k : ℤ) (j : ℕ) :
    (canonicalCap δ p E r k 0).component j = 0 := sorry

/-- Every component of the canonical Chern-class cap is additive in the input
cycle. -/
theorem canonicalCap_component_add
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (k : ℤ) (j : ℕ)
    (α β : CycleGroup X (p.relativeDimensionFunction δ) k) :
    (canonicalCap δ p E r k (α + β)).component j =
      (canonicalCap δ p E r k α).component j +
        (canonicalCap δ p E r k β).component j := sorry

/-- The cycle-level additive homomorphism defined by the `j`th intrinsic Chern
component. -/
noncomputable def cycleComponent
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (j : ℕ) (k : ℤ) :
    CycleGroup X (p.relativeDimensionFunction δ) k →+
      @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance (k - (j : ℤ)) :=
  { toFun := fun α ↦ (canonicalCap δ p E r k α).component j
    map_zero' := canonicalCap_component_zero_cycle δ p E r k j
    map_add' := canonicalCap_component_add δ p E r k j }

/-- Evaluation of the cycle-level Chern component is the corresponding
component of the canonical intrinsic cap. -/
theorem cycleComponent_apply
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (j : ℕ) (k : ℤ)
    (α : CycleGroup X (p.relativeDimensionFunction δ) k) :
    cycleComponent δ p E r j k α =
      (canonicalCap δ p E r k α).component j := sorry

/-- The bounded family of cycle-level Chern components satisfies the
projective-bundle characterization. -/
theorem cycleComponent_isChernClassCap
    {S X P : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E) (k : ℤ) :
    ChowGroup.ProjectiveBundle.IsChernClassCap δ p E r π hπ k
      (fun j ↦ cycleComponent δ p E r (j : ℕ) k) := sorry

/-- Rational-equivalence boundaries lie in the kernel of every cycle-level
Chern component. -/
theorem cycleComponent_boundaries_le_ker
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (j : ℕ) (k : ℤ) :
    @RationalEquivalence.boundaries X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k ≤
      (cycleComponent δ p E r j k).ker := sorry

/-- Intersection with the `j`th Chern class as an additive map on relative Chow
groups. -/
noncomputable def chowCap
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (j : ℕ) (k : ℤ) :
    @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k →+
      @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance (k - (j : ℤ)) :=
  QuotientAddGroup.lift
    (@RationalEquivalence.boundaries X (LocallyOfFiniteType.isLocallyNoetherian p)
      (p.relativeDimensionFunction δ) inferInstance k)
    (cycleComponent δ p E r j k)
    (cycleComponent_boundaries_le_ker δ p E r j k)

/-- The Chow-level Chern cap on a cycle class is the corresponding component
of the canonical intrinsic cap. -/
theorem chowCap_chowClass
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (j : ℕ) (k : ℤ)
    (α : CycleGroup X (p.relativeDimensionFunction δ) k) :
    chowCap δ p E r j k
        (@chowClass X (LocallyOfFiniteType.isLocallyNoetherian p)
          (p.relativeDimensionFunction δ) inferInstance k α) =
      (canonicalCap δ p E r k α).component j := sorry

/-- The cap family obtained by intersecting with the `j`th Chern class of the
pulled-back finite locally free module. -/
noncomputable def cap
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [hE : Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (j : ℕ) :
    BivariantClass.CapFamily δ (𝟙 (Over.mk p)) (j : ℤ) :=
  fun {X' _} _ _ f _ g _ square k ↦
    (@chowCap S X'.left inferInstance δ inferInstance X'.hom inferInstance
      ((Scheme.Modules.pullback f.left).obj E) r
      (@Scheme.Modules.pullback_isFiniteLocallyFreeOfRank X'.left X f.left E r hE)
      j k).comp
        ((RelativeChow.castDegree δ (Int.sub_zero k)).comp
          (identityCap δ p f _ g square k))

/-- Evaluation of the Chern cap family is Chern intersection after transport
across the displayed identity pullback square. -/
theorem cap_apply
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [hE : Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (j : ℕ)
    {X' Y' : Over S} [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (f : X' ⟶ Over.mk p) (f' : X' ⟶ Y') (g : Y' ⟶ Over.mk p)
    [LocallyOfFiniteType g.left]
    (square : IsPullback f.left f'.left (𝟙 X) g.left) (k : ℤ) :
    cap δ p E r j f f' g square k =
      (@chowCap S X'.left inferInstance δ inferInstance X'.hom inferInstance
        ((Scheme.Modules.pullback f.left).obj E) r
        (@Scheme.Modules.pullback_isFiniteLocallyFreeOfRank X'.left X f.left E r hE)
        j k).comp
          ((RelativeChow.castDegree δ (Int.sub_zero k)).comp
            (identityCap δ p f f' g square k)) := sorry

/-- Chern-component intersection commutes with proper pushforward. -/
theorem capMapProper
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (j : ℕ) :
    BivariantClass.CompatibleWithProperPushforward δ (cap δ p E r j) := sorry

/-- Chern-component intersection commutes with flat pullback. -/
theorem capPullbackFlat
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (j : ℕ) :
    BivariantClass.CompatibleWithFlatPullback δ (cap δ p E r j) := sorry

/-- Chern-component intersection commutes with effective-Cartier Gysin
pullback. -/
theorem capGysinCartier
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (j : ℕ) :
    BivariantClass.CompatibleWithCartierGysin δ (cap δ p E r j) := sorry

/-- The degree-`j` Chow-cohomology class defined by the `j`th Chern class of a
finite locally free module. -/
noncomputable def component
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (j : ℕ) :
    degree δ p (j : ℤ) where
  cap := cap δ p E r j
  map_proper := capMapProper δ p E r j
  pullback_flat := capPullbackFlat δ p E r j
  gysin_cartier := capGysinCartier δ p E r j

/-- The cap family of a Chern component is its canonical Chern cap family. -/
theorem component_cap
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (j : ℕ)
    {X' Y' : Over S} [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (f : X' ⟶ Over.mk p) (f' : X' ⟶ Y') (g : Y' ⟶ Over.mk p)
    [LocallyOfFiniteType g.left]
    (square : IsPullback f.left f'.left (𝟙 X) g.left) (k : ℤ) :
    (component δ p E r j).cap f f' g square k =
      cap δ p E r j f f' g square k := sorry

/-- On the canonical identity square, a Chern component acts by its canonical
Chow-level cap operation after pullback. -/
theorem component_apply
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [hE : Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (j : ℕ)
    {X' : Over S} [LocallyOfFiniteType X'.hom] (f : X' ⟶ Over.mk p)
    (k : ℤ) (α : RelativeChow δ X' k) :
    (component δ p E r j).cap f (𝟙 X') f IsPullback.of_id_snd k α =
      @chowCap S X'.left inferInstance δ inferInstance X'.hom inferInstance
        ((Scheme.Modules.pullback f.left).obj E) r
        (@Scheme.Modules.pullback_isFiniteLocallyFreeOfRank X'.left X f.left E r hE)
        j k α := sorry

/-- Every Chern component above the rank is the zero bivariant class. -/
theorem component_eq_zero
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (j : ℕ) (hj : r < j) :
    component δ p E r j = 0 := sorry

end AlgebraicGeometry.ChowCohomology.ChernClass
