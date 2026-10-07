module

public import ReasLib.AlgebraicGeometry.ChowCohomology.Completion
public import Mathlib.Algebra.Group.Center
public import ReasLib.AlgebraicGeometry.BivariantClass.Restriction
public import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Biproduct
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Tensor
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators DirectSum MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.ChernClass

section Homogeneous

variable {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
variable [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]

/-- Embed a homogeneous nonnegative Chow-cohomology class in the full nonnegative ring. -/
def homogeneous (i : ℕ) (c : ChowCohomology.Nonnegative.degree δ p i) :
    ChowCohomology.Nonnegative.ring δ p :=
  DirectSum.of (ChowCohomology.Nonnegative.degree δ p) i c

end Homogeneous

variable {S : Scheme.{u}} (δ : S → ℤ)
variable [UniversallyCatenary S] [IsDimensionFunction δ]

/-- Restriction of a homogeneous operational Chow class along an over-morphism. -/
def restrictComponent {Y Z : Over S} [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (g : Y ⟶ Z) (i : ℕ) :
    BivariantClass δ (𝟙 Z) (i : ℤ) → BivariantClass δ (𝟙 Y) (i : ℤ) :=
  BivariantClass.restrict δ g (𝟙 Y) g IsPullback.of_id_snd (i : ℤ)

/-- `restrictComponent` is the identity-square specialization of bivariant restriction. -/
theorem restrictComponent_apply {Y Z : Over S} [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (g : Y ⟶ Z) (i : ℕ)
    (c : BivariantClass δ (𝟙 Z) (i : ℤ)) :
    restrictComponent δ g i c =
      BivariantClass.restrict δ g (𝟙 Y) g IsPullback.of_id_snd (i : ℤ) c := sorry

/-- A base-wide Chern-class operation, anchored at `p`, characterized by pullback
naturality, the canonical first-Chern cap operation, Whitney sums, and an injective
splitting principle. The tensor-twist identity is deliberately not one of the fields. -/
structure Theory {X : Scheme.{u}} (p : X ⟶ S) [LocallyOfFiniteType p] where
  /-- The degree-`i` Chern class of a module on an `S`-scheme. -/
  baseComponent (Y : Over S) [LocallyOfFiniteType Y.hom]
    (E : Y.left.Modules) (i : ℕ) : BivariantClass δ (𝟙 Y) (i : ℤ)
  /-- Chern classes commute with pullback between `S`-schemes. -/
  component_pullback {Y Z : Over S} [LocallyOfFiniteType Y.hom]
      [LocallyOfFiniteType Z.hom] (g : Y ⟶ Z) (E : Z.left.Modules) (i : ℕ) :
    restrictComponent δ g i (baseComponent Z E i) =
      baseComponent Y ((Scheme.Modules.pullback g.left).obj E) i
  /-- On line bundles, the degree-one component is the canonical first-Chern cap
  operation on every base change. -/
  component_one_cap (Y : Over S) [LocallyOfFiniteType Y.hom]
      (L : Y.left.Modules) [Scheme.Modules.Invertible L]
      {Z : Over S} [LocallyOfFiniteType Z.hom] (g : Z ⟶ Y)
      (k : ℤ) (a : RelativeChow δ Z k) :
    (baseComponent Y L 1).cap g (𝟙 Z) g IsPullback.of_id_snd k a =
      ChowGroup.firstChernClassCap δ Z
        ((Scheme.Modules.pullback g.left).obj L) k a
  /-- The degree-zero Chern class of a finite locally free module is the unit. -/
  component_zero (Y : Over S) [LocallyOfFiniteType Y.hom]
      (E : Y.left.Modules) (hE : E.IsFiniteLocallyFree) :
    baseComponent Y E 0 = ChowCohomology.one δ Y.hom
  /-- Chern classes are invariant under isomorphism of finite locally free modules. -/
  component_iso (Y : Over S) [LocallyOfFiniteType Y.hom]
      {E F : Y.left.Modules} (hE : E.IsFiniteLocallyFree)
      (hF : F.IsFiniteLocallyFree) (e : E ≅ F) (i : ℕ) :
    baseComponent Y E i = baseComponent Y F i
  /-- The degree-`i` Chern class vanishes above the rank. -/
  component_eq_zero_of_rank_lt (Y : Over S) [LocallyOfFiniteType Y.hom]
      (E : Y.left.Modules) (r : ℕ) (hE : E.IsFiniteLocallyFreeOfRank r)
      (i : ℕ) (hi : r < i) :
    baseComponent Y E i = BivariantClass.pointwiseZero δ (𝟙 Y) (i : ℤ)
  /-- Every homogeneous Chern class is central in operational Chow cohomology. -/
  component_mem_center (Y : Over S) [LocallyOfFiniteType Y.hom]
      (E : Y.left.Modules) (i : ℕ) :
    homogeneous δ Y.hom i (baseComponent Y E i) ∈
      Set.center (ChowCohomology.Nonnegative.ring δ Y.hom)
  /-- The Whitney sum formula for a biproduct of finite locally free modules. -/
  component_biprod (Y : Over S) [LocallyOfFiniteType Y.hom]
      (E F : Y.left.Modules) (hE : E.IsFiniteLocallyFree)
      (hF : F.IsFiniteLocallyFree) (i : ℕ) :
    homogeneous δ Y.hom i (baseComponent Y (E ⊞ F) i) =
      ∑ j ∈ Finset.range (i + 1),
        homogeneous δ Y.hom j (baseComponent Y E j) *
          homogeneous δ Y.hom (i - j) (baseComponent Y F (i - j))
  /-- First Chern classes turn tensor products of invertible modules into sums. -/
  component_one_tensor (Y : Over S) [LocallyOfFiniteType Y.hom]
      (L M : Y.left.Modules) (hL : L.Invertible) (hM : M.Invertible) :
    baseComponent Y (L ⊗ M) 1 =
      BivariantClass.pointwiseAdd δ (𝟙 Y) 1
        (baseComponent Y L 1) (baseComponent Y M 1)
  /-- Every constant-rank finite locally free module splits into line bundles after a
  pullback which is injective on every homogeneous operational Chow group. -/
  splitting_principle (Y : Over S) [LocallyOfFiniteType Y.hom]
      (E : Y.left.Modules) (r : ℕ) [E.IsFiniteLocallyFreeOfRank r] :
    ∃ (Z : Over S) (hZ : LocallyOfFiniteType Z.hom) (g : Z ⟶ Y)
        (lines : Fin r → Z.left.Modules),
      (∀ a, Scheme.Modules.Invertible (lines a)) ∧
        Nonempty ((Scheme.Modules.pullback g.left).obj E ≅ ∐ lines) ∧
          ∀ i : ℕ, Function.Injective
            (@restrictComponent S δ inferInstance inferInstance Z Y
              hZ inferInstance g i)

namespace Theory

/-- The Chern-class component on the scheme at which a theory is anchored. -/
def component {S : Scheme.{u}} [UniversallyCatenary S]
    {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Scheme.{u}} {p : X ⟶ S} [LocallyOfFiniteType p]
    (classes : Theory δ p) (E : X.Modules) (i : ℕ) :
    ChowCohomology.Nonnegative.degree δ p i :=
  classes.baseComponent (Over.mk p) E i

/-- The anchored component is the corresponding value of the base-wide operation. -/
theorem component_def {S : Scheme.{u}} [UniversallyCatenary S]
    {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Scheme.{u}} {p : X ⟶ S} [LocallyOfFiniteType p]
    (classes : Theory δ p) (E : X.Modules) (i : ℕ) :
    classes.component E i = classes.baseComponent (Over.mk p) E i := sorry

/-- Build a Chern-class theory from base-wide components satisfying its canonical
naturality, normalization, Whitney-sum, and splitting-principle specifications. -/
def ofComponents
    {X : Scheme.{u}} (p : X ⟶ S) [LocallyOfFiniteType p]
    (baseComponent : ∀ (Y : Over S) [LocallyOfFiniteType Y.hom],
      Y.left.Modules → (i : ℕ) → BivariantClass δ (𝟙 Y) (i : ℤ))
    (component_pullback : ∀ {Y Z : Over S} [LocallyOfFiniteType Y.hom]
      [LocallyOfFiniteType Z.hom] (g : Y ⟶ Z) (E : Z.left.Modules) (i : ℕ),
      restrictComponent δ g i (baseComponent Z E i) =
        baseComponent Y ((Scheme.Modules.pullback g.left).obj E) i)
    (component_one_cap : ∀ (Y : Over S) [LocallyOfFiniteType Y.hom]
      (L : Y.left.Modules) [Scheme.Modules.Invertible L]
      {Z : Over S} [LocallyOfFiniteType Z.hom] (g : Z ⟶ Y)
      (k : ℤ) (a : RelativeChow δ Z k),
      (baseComponent Y L 1).cap g (𝟙 Z) g IsPullback.of_id_snd k a =
        ChowGroup.firstChernClassCap δ Z
          ((Scheme.Modules.pullback g.left).obj L) k a)
    (component_zero : ∀ (Y : Over S) [LocallyOfFiniteType Y.hom]
      (E : Y.left.Modules), E.IsFiniteLocallyFree →
        baseComponent Y E 0 = ChowCohomology.one δ Y.hom)
    (component_iso : ∀ (Y : Over S) [LocallyOfFiniteType Y.hom]
      {E F : Y.left.Modules}, E.IsFiniteLocallyFree → F.IsFiniteLocallyFree →
        (E ≅ F) → ∀ i, baseComponent Y E i = baseComponent Y F i)
    (component_eq_zero_of_rank_lt : ∀ (Y : Over S) [LocallyOfFiniteType Y.hom]
      (E : Y.left.Modules) (r : ℕ), E.IsFiniteLocallyFreeOfRank r →
        ∀ i, r < i → baseComponent Y E i =
          BivariantClass.pointwiseZero δ (𝟙 Y) (i : ℤ))
    (component_mem_center : ∀ (Y : Over S) [LocallyOfFiniteType Y.hom]
      (E : Y.left.Modules) (i : ℕ),
      homogeneous δ Y.hom i (baseComponent Y E i) ∈
        Set.center (ChowCohomology.Nonnegative.ring δ Y.hom))
    (component_biprod : ∀ (Y : Over S) [LocallyOfFiniteType Y.hom]
      (E F : Y.left.Modules), E.IsFiniteLocallyFree → F.IsFiniteLocallyFree → ∀ i,
        homogeneous δ Y.hom i (baseComponent Y (E ⊞ F) i) =
          ∑ j ∈ Finset.range (i + 1),
            homogeneous δ Y.hom j (baseComponent Y E j) *
              homogeneous δ Y.hom (i - j) (baseComponent Y F (i - j)))
    (component_one_tensor : ∀ (Y : Over S) [LocallyOfFiniteType Y.hom]
      (L M : Y.left.Modules), L.Invertible → M.Invertible →
        baseComponent Y (L ⊗ M) 1 =
          BivariantClass.pointwiseAdd δ (𝟙 Y) 1
            (baseComponent Y L 1) (baseComponent Y M 1))
    (splitting_principle : ∀ (Y : Over S) [LocallyOfFiniteType Y.hom]
      (E : Y.left.Modules) (r : ℕ) [E.IsFiniteLocallyFreeOfRank r],
      ∃ (Z : Over S) (hZ : LocallyOfFiniteType Z.hom) (g : Z ⟶ Y)
          (lines : Fin r → Z.left.Modules),
        (∀ a, Scheme.Modules.Invertible (lines a)) ∧
          Nonempty ((Scheme.Modules.pullback g.left).obj E ≅ ∐ lines) ∧
            ∀ i : ℕ, Function.Injective
              (@restrictComponent S δ inferInstance inferInstance Z Y
                hZ inferInstance g i)) :
    Theory δ p where
  baseComponent := baseComponent
  component_pullback := component_pullback
  component_one_cap := component_one_cap
  component_zero := component_zero
  component_iso := component_iso
  component_eq_zero_of_rank_lt := component_eq_zero_of_rank_lt
  component_mem_center := component_mem_center
  component_biprod := component_biprod
  component_one_tensor := component_one_tensor
  splitting_principle := splitting_principle

end Theory

end AlgebraicGeometry.ChernClass
