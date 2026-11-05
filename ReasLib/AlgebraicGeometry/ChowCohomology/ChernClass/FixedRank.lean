/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveBundle.ChernClassCap.Intrinsic
public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveBundle.ChernClassCap.RationalEquivalence
public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveBundle.ChernClassCap.Pushforward
public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveBundle.ChernClassCap.FlatPullback
public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveBundle.ChernClassCap.Gysin
public import ReasLib.AlgebraicGeometry.BivariantClass.Descent
public import ReasLib.AlgebraicGeometry.ChowCohomology.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import Mathlib.Algebra.Group.Center
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Commutation

/-!
# Operational Chern classes in fixed rank

Deprecated bounded-index specializations of the canonical natural-number-indexed
operations in `ChowCohomology.ChernClass`. No separate intrinsic cap is selected here.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.ChernClass.FixedRank

/-- The intrinsically characterized Chern-class cap attached to a cycle. -/
@[deprecated ChowCohomology.ChernClass.canonicalCap (since := "2026-11-04")]
noncomputable abbrev cycleCap
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (k : ℤ)
    (α : CycleGroup X (p.relativeDimensionFunction δ) k) :
    ChowGroup.ChernClassCap δ p E r k α :=
  ChowCohomology.ChernClass.canonicalCap δ p E r k α

/-- The intrinsic characterization makes `cycleCap` equal to every realization. -/
theorem cycleCap_eq
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (k : ℤ)
    (α : CycleGroup X (p.relativeDimensionFunction δ) k)
    (c : ChowGroup.ChernClassCap δ p E r k α) : cycleCap δ p E r k α = c :=
  ChowCohomology.ChernClass.canonicalCap_eq δ p E r k α c

/-- The zeroth component of `cycleCap` is the Chow class of the input cycle. -/
theorem cycleCap_component_zero
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (k : ℤ)
    (α : CycleGroup X (p.relativeDimensionFunction δ) k) :
    (cycleCap δ p E r k α).component 0 =
      @ChowGroup.reindex X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k (k - (0 : ℕ))
        (sub_zero k).symm
        (@AlgebraicGeometry.chowClass X (LocallyOfFiniteType.isLocallyNoetherian p)
          (p.relativeDimensionFunction δ) inferInstance k α) :=
  ChowCohomology.ChernClass.canonicalCap_component_zero δ p E r k α

/-- Components of `cycleCap` above the rank vanish. -/
theorem cycleCap_component_eq_zero_of_rank_lt
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (k : ℤ)
    (α : CycleGroup X (p.relativeDimensionFunction δ) k) (j : ℕ) (hj : r < j) :
    (cycleCap δ p E r k α).component j = 0 :=
  ChowCohomology.ChernClass.canonicalCap_component_eq_zero δ p E r k α j hj

/-- Every selected intrinsic Chern component sends the zero cycle to zero. -/
theorem cycleCap_component_zero_cycle
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (k : ℤ) (i : Fin (r + 1)) :
    (cycleCap δ p E r k 0).component (i : ℕ) = 0 :=
  ChowCohomology.ChernClass.canonicalCap_component_zero_cycle δ p E r k (i : ℕ)

/-- Every selected intrinsic Chern component is additive in the input cycle. -/
theorem cycleCap_component_add
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (k : ℤ) (i : Fin (r + 1))
    (α β : CycleGroup X (p.relativeDimensionFunction δ) k) :
    (cycleCap δ p E r k (α + β)).component (i : ℕ) =
      (cycleCap δ p E r k α).component (i : ℕ) +
        (cycleCap δ p E r k β).component (i : ℕ) :=
  ChowCohomology.ChernClass.canonicalCap_component_add δ p E r k (i : ℕ) α β

/-- The cycle-level additive homomorphism defined by the `i`th intrinsic Chern cap. -/
@[deprecated ChowCohomology.ChernClass.cycleComponent (since := "2026-11-04")]
noncomputable abbrev componentHom
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [hE : Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (k : ℤ) (i : Fin (r + 1)) :
    CycleGroup X (p.relativeDimensionFunction δ) k →+
      @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance (k - (i : ℕ)) :=
  ChowCohomology.ChernClass.cycleComponent δ p E r (i : ℕ) k

/-- Evaluation of `componentHom` is the corresponding intrinsic component. -/
theorem componentHom_apply
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [hE : Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (k : ℤ) (i : Fin (r + 1))
    (α : CycleGroup X (p.relativeDimensionFunction δ) k) :
    componentHom δ p E r k i α =
      (cycleCap δ p E r k α).component (i : ℕ) := by
  rfl

/-- The complete family of cycle-level component maps satisfies the
projective-bundle characterization. -/
theorem componentHom_isChernClassCap
    {S X P : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [hE : Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E) (k : ℤ) :
    ChowGroup.ProjectiveBundle.IsChernClassCap δ p E r π hπ k
      (componentHom δ p E r k) :=
  ChowCohomology.ChernClass.cycleComponent_isChernClassCap δ p E r π hπ k

/-- Rational-equivalence boundaries lie in the kernel of every cycle-level
Chern component. -/
theorem componentHom_boundaries_le_ker
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [hE : Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (k : ℤ) (i : Fin (r + 1)) :
    @AlgebraicGeometry.RationalEquivalence.boundaries X
        (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k ≤
      (componentHom δ p E r k i).ker :=
  ChowCohomology.ChernClass.cycleComponent_boundaries_le_ker δ p E r (i : ℕ) k

/-- Intersection with the `i`th Chern class on relative Chow groups. -/
@[deprecated ChowCohomology.ChernClass.chowCap (since := "2026-11-04")]
noncomputable abbrev chernClassCap
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [hE : Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (i : Fin (r + 1)) (k : ℤ) :
    @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k →+
      @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance (k - (i : ℕ)) :=
  ChowCohomology.ChernClass.chowCap δ p E r (i : ℕ) k

/-- The Chow-level cap on a cycle class is its intrinsic cycle-level component. -/
theorem chernClassCap_chowClass
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [hE : Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (i : Fin (r + 1)) (k : ℤ)
    (α : CycleGroup X (p.relativeDimensionFunction δ) k) :
    chernClassCap δ p E r i k
        (@AlgebraicGeometry.chowClass X (LocallyOfFiniteType.isLocallyNoetherian p)
          (p.relativeDimensionFunction δ) inferInstance k α) =
      (cycleCap δ p E r k α).component (i : ℕ) :=
  ChowCohomology.ChernClass.chowCap_chowClass δ p E r (i : ℕ) k α

/-- The cap family obtained by intersecting with the selected Chern component of
the pulled-back finite locally free module. -/
@[deprecated ChowCohomology.ChernClass.cap (since := "2026-11-04")]
noncomputable abbrev cap
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [hE : Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (i : Fin (r + 1)) :
    BivariantClass.CapFamily δ (𝟙 (Over.mk p)) (i : ℤ) :=
  ChowCohomology.ChernClass.cap δ p E r (i : ℕ)

/-- Evaluation of `cap` is Chern intersection after transport across the displayed
identity pullback square. -/
theorem cap_apply
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [hE : Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (i : Fin (r + 1))
    {X' Y' : Over S} [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (f : X' ⟶ Over.mk p) (f' : X' ⟶ Y') (g : Y' ⟶ Over.mk p)
    [LocallyOfFiniteType g.left]
    (square : IsPullback f.left f'.left (𝟙 X) g.left) (k : ℤ) :
    cap δ p E r i f f' g square k =
      (@chernClassCap S X'.left inferInstance δ inferInstance
        X'.hom inferInstance ((Scheme.Modules.pullback f.left).obj E) r
        (@Scheme.Modules.pullback_isFiniteLocallyFreeOfRank X'.left X f.left E r hE)
        i k).comp
          ((RelativeChow.castDegree δ (Int.sub_zero k)).comp
            (ChowCohomology.identityCap δ p f f' g square k)) := by
  rfl

/-- Chern-component intersection commutes with proper pushforward. -/
theorem capMapProper
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (i : Fin (r + 1)) :
    BivariantClass.CompatibleWithProperPushforward δ (cap δ p E r i) :=
  ChowCohomology.ChernClass.capMapProper δ p E r (i : ℕ)

/-- Chern-component intersection commutes with flat pullback. -/
theorem capPullbackFlat
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (i : Fin (r + 1)) :
    BivariantClass.CompatibleWithFlatPullback δ (cap δ p E r i) :=
  ChowCohomology.ChernClass.capPullbackFlat δ p E r (i : ℕ)

/-- Chern-component intersection commutes with effective-Cartier Gysin pullback. -/
theorem capGysinCartier
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (i : Fin (r + 1)) :
    BivariantClass.CompatibleWithCartierGysin δ (cap δ p E r i) :=
  ChowCohomology.ChernClass.capGysinCartier δ p E r (i : ℕ)

/-- The degree-`i` operational Chern class of a finite locally free module of rank `r`. -/
@[deprecated ChowCohomology.ChernClass.component (since := "2026-11-04")]
noncomputable abbrev component
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (i : Fin (r + 1)) :
    ChowCohomology.degree δ p (i : ℤ) :=
  ChowCohomology.ChernClass.component δ p E r (i : ℕ)

/-- The cap family of `component` is the canonical Chern-component cap family. -/
theorem component_cap
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (i : Fin (r + 1))
    {X' Y' : Over S} [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (f : X' ⟶ Over.mk p) (f' : X' ⟶ Y') (g : Y' ⟶ Over.mk p)
    [LocallyOfFiniteType g.left]
    (square : IsPullback f.left f'.left (𝟙 X) g.left) (k : ℤ) :
    (component δ p E r i).cap f f' g square k =
      cap δ p E r i f f' g square k := by
  rfl

/-- On an identity test square, `component` acts by the corresponding Chern cap. -/
theorem component_apply
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [hE : Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (i : Fin (r + 1))
    {X' : Over S} [LocallyOfFiniteType X'.hom] (f : X' ⟶ Over.mk p)
    (k : ℤ) (α : RelativeChow δ X' k) :
    (component δ p E r i).cap f (𝟙 X') f IsPullback.of_id_snd k α =
      @chernClassCap S X'.left inferInstance δ inferInstance
        X'.hom inferInstance ((Scheme.Modules.pullback f.left).obj E) r
        (@Scheme.Modules.pullback_isFiniteLocallyFreeOfRank X'.left X f.left E r hE)
        i k α :=
  ChowCohomology.ChernClass.component_apply δ p E r (i : ℕ) f k α

/-- Every fixed-rank operational Chern component is central in Chow cohomology. -/
@[deprecated ChowCohomology.ChernClass.component_mem_center (since := "2026-11-04")]
theorem component_mem_center
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (i : Fin (r + 1)) :
    DirectSum.of (ChowCohomology.degree δ p) ((i : ℕ) : ℤ) (component δ p E r i) ∈
      Set.center (ChowCohomology.ring δ p) :=
  ChowCohomology.ChernClass.component_mem_center δ p E r (i : ℕ)

/-- The legacy operation is definitionally the canonical operation. -/
@[simp]
theorem cycleCap_eq_canonical
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (k : ℤ)
    (α : CycleGroup X (p.relativeDimensionFunction δ) k) :
    cycleCap δ p E r k α = ChowCohomology.ChernClass.canonicalCap δ p E r k α := rfl

/-- The legacy operation is definitionally the canonical operation. -/
@[simp]
theorem componentHom_eq
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [hE : Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (k : ℤ) (i : Fin (r + 1)) :
    componentHom δ p E r k i = ChowCohomology.ChernClass.cycleComponent δ p E r (i : ℕ) k := rfl

/-- The legacy operation is definitionally the canonical operation. -/
@[simp]
theorem chernClassCap_eq
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [hE : Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (i : Fin (r + 1)) (k : ℤ) :
    chernClassCap δ p E r i k = ChowCohomology.ChernClass.chowCap δ p E r (i : ℕ) k := rfl

/-- The legacy operation is definitionally the canonical operation. -/
@[simp]
theorem cap_eq
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [hE : Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (i : Fin (r + 1)) :
    @Eq (BivariantClass.CapFamily δ (𝟙 (Over.mk p)) ((i : ℕ) : ℤ))
      (cap δ p E r i) (ChowCohomology.ChernClass.cap δ p E r (i : ℕ)) := rfl

/-- The legacy operation is definitionally the canonical operation. -/
@[simp]
theorem component_eq
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (i : Fin (r + 1)) :
    component δ p E r i = ChowCohomology.ChernClass.component δ p E r (i : ℕ) := rfl

end AlgebraicGeometry.ChernClass.FixedRank
