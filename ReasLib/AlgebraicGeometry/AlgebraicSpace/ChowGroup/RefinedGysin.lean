/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernCycle
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ZeroSchemeFactor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.AssociatedCycle
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.PointClosure
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Closed.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.Point
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.ClosedImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Subspace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.Composition

/-! # Refined Gysin maps for zero schemes of invertible-module sections -/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Function Set Topology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ChowGroup.RefinedGysin

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]

/-- The zero scheme of an invertible-module section is quasi-separated over a
base over which the ambient space is quasi-separated. -/
instance zeroScheme_quasiSeparated (pX : X ⟶ B) [QuasiSeparated pX]
    (L : X.Modules) [isInvertibleObject L] (s : L.sections) :
    QuasiSeparated (zeroSchemeι L s ≫ pX) :=
  quasiSeparated_closedSubspace_comp (zeroScheme L s) pX

/-- The zero scheme of an invertible-module section is locally of finite type
over a base over which the ambient space is locally of finite type. -/
instance zeroScheme_locallyOfFiniteType (pX : X ⟶ B) [LocallyOfFiniteType pX]
    (L : X.Modules) [isInvertibleObject L] (s : L.sections) :
    LocallyOfFiniteType (zeroSchemeι L s ≫ pX) :=
  locallyOfFiniteType_closedSubspace_comp (zeroScheme L s) pX

end AlgebraicGeometry.AlgebraicSpace.ChowGroup.RefinedGysin

namespace AlgebraicGeometry.AlgebraicSpace.Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
  (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
  (δ : Points B → ℤ) [IsDimensionFunction δ] (k : ℤ)
  (L : X.Modules) [isInvertibleObject L] (s : L.sections)

/-- The associated cycle of the scheme-theoretic intersection of a point
closure with the zero scheme, including its intersection multiplicities. -/
def gysinIntersectionCycle (x : Points X) :
    Function.locallyFinsupp (Points (zeroScheme L s).X) ℤ :=
  @ClosedSubspace.associatedCycle S (zeroScheme L s).X
    (LocallyOfFiniteType.isLocallyNoetherian (zeroSchemeι L s ≫ f))
    ((ClosedSubspace.pointClosure x).inverseImageSubspace (zeroSchemeι L s))
    (relativeDimensionFunction (zeroSchemeι L s ≫ f) δ) k

/-- The associated intersection cycle is supported in relative degree `k`. -/
theorem gysinIntersectionCycle_mem (x : Points X) :
    gysinIntersectionCycle f δ k L s x ∈ cycleGroup (zeroSchemeι L s ≫ f) δ k :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom

namespace AlgebraicGeometry.AlgebraicSpace.ChowGroup.RefinedGysin

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]

variable (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
  (δ : Points B → ℤ) [IsDimensionFunction δ]
  (L : X.Modules) [isInvertibleObject L] (s : L.sections)

/-- A section vanishes on a reduced point closure precisely when that closure
is supported in its zero scheme. -/
theorem contained_iff_support (x : Points X) :
    IntersectionTheory.ZeroSchemeFactor.VanishesOn L s (PointClosure.ι x) ↔
      (ClosedSubspace.pointClosure x).pointsSet ⊆ (zeroScheme L s).pointsSet := sorry

/-- A section vanishes on the reduced closure of a point precisely when the
point lies in its zero scheme. -/
theorem contained_iff_mem (x : Points X) :
    IntersectionTheory.ZeroSchemeFactor.VanishesOn L s (PointClosure.ι x) ↔
      x ∈ (zeroScheme L s).pointsSet := by
  rw [contained_iff_support]
  change Set.range (Points.map (PointClosure.ι x)) ⊆ (zeroScheme L s).pointsSet ↔ _
  rw [PointClosure.range_ι, PointClosure.coe_closedSubset]
  constructor
  · intro h
    exact h (subset_closure (Set.mem_singleton x))
  · intro h
    exact closure_minimal (Set.singleton_subset_iff.mpr h) (zeroScheme L s).isClosed_pointsSet

/-- The generic point of a reduced point closure has the same relative degree
as its image in the ambient space. -/
theorem generic_degree (k : ℤ) (x : Points X)
    (hx : Hom.relativeDimensionFunction pX δ x = k + 1) :
    Hom.relativeDimensionFunction (PointClosure.ι x ≫ pX) δ
      (PointClosure.generic x) = k + 1 := sorry

/-- The fundamental cycle of the reduced integral closure of a point. -/
def fundamental (k : ℤ) (x : Points X)
    (hx : Hom.relativeDimensionFunction pX δ x = k + 1) :
    Hom.cycleGroup (PointClosure.ι x ≫ pX) δ (k + 1) :=
  ⟨Hom.pointCycle (PointClosure.generic x),
    Hom.pointCycle_mem (PointClosure.ι x ≫ pX) δ k (PointClosure.generic x)
      (generic_degree pX δ k x hx)⟩

/-- The contained point-closure contribution is the pushforward of its
restricted first Chern cycle along the induced zero-scheme immersion. -/
def containedGenerator (k : ℤ) (x : Points X)
    (h : IntersectionTheory.ZeroSchemeFactor.VanishesOn L s (PointClosure.ι x)) :
    Function.locallyFinsupp (Points (zeroScheme L s).X) ℤ := by
  exact Hom.closedImmersionCyclePushforward
    (IntersectionTheory.ZeroSchemeFactor.lift L s (PointClosure.ι x) h)
    (hClosed := IntersectionTheory.ZeroSchemeFactor.lift_isClosedImmersion
      L s (PointClosure.ι x) h)
    (@Hom.firstChernCycle S B (PointClosure.space x) inferInstance inferInstance
      (PointClosure.ι x ≫ pX) (Hom.closure_quasiSeparated pX x)
      (Hom.closure_locallyOfFiniteType pX x) δ inferInstance
      ((Modules.pullback (PointClosure.ι x)).obj L)
      (Modules.isInvertibleObject_pullback (PointClosure.ι x) L) k
      (Hom.pointCycle (PointClosure.generic x)))

/-- The refined intersection of a point closure with a section: on a contained
closure use its restricted first Chern cycle; otherwise use the associated
cycle of its inverse image in the zero scheme. -/
def generator (k : ℤ) (x : Points X) :
    Function.locallyFinsupp (Points (zeroScheme L s).X) ℤ := by
  classical
  exact if h : IntersectionTheory.ZeroSchemeFactor.VanishesOn L s (PointClosure.ι x) then
    containedGenerator pX δ L s k x h
  else
    Hom.gysinIntersectionCycle pX δ k L s x

/-- Off the zero scheme, a generator is the associated intersection cycle. -/
theorem generator_of_not_mem (k : ℤ) (x : Points X)
    (hmem : x ∉ (zeroScheme L s).pointsSet) :
    generator pX δ L s k x = Hom.gysinIntersectionCycle pX δ k L s x := by
  classical
  have h : ¬IntersectionTheory.ZeroSchemeFactor.VanishesOn L s (PointClosure.ι x) :=
    fun hc ↦ hmem ((contained_iff_mem L s x).mp hc)
  simp only [generator, dif_neg h]

/-- On the zero scheme, a generator is its contained first Chern contribution. -/
theorem generator_of_mem (k : ℤ) (x : Points X)
    (hmem : x ∈ (zeroScheme L s).pointsSet) :
    generator pX δ L s k x =
      containedGenerator pX δ L s k x ((contained_iff_mem L s x).mpr hmem) := by
  classical
  simp only [generator, dif_pos ((contained_iff_mem L s x).mpr hmem)]

/-- Coefficient-weighted refined intersections of a locally finite cycle form
a locally finite family on the zero scheme. -/
theorem generatorTermsLocallyFinite (k : ℤ)
    (α : Function.locallyFinsupp (Points X) ℤ) :
    LocallyFinite fun x : Points X ↦
      (if Hom.relativeDimensionFunction pX δ x = k + 1 then
        α x • generator pX δ L s k x else 0).support := sorry

/-- Refined intersection of cycles is the locally finite sum of their
coefficient-weighted point-closure intersections. -/
def cycle (k : ℤ) (α : Function.locallyFinsupp (Points X) ℤ) :
    Function.locallyFinsupp (Points (zeroScheme L s).X) ℤ :=
  AlgebraicCycle.locallyFiniteSum
    (fun x : Points X ↦ if Hom.relativeDimensionFunction pX δ x = k + 1 then
      α x • generator pX δ L s k x else 0)
    (generatorTermsLocallyFinite pX δ L s k α)

/-- Each refined-intersection coefficient is the finite sum of the weighted
generator coefficients at that point. -/
theorem cycle_apply (k : ℤ) (α : Function.locallyFinsupp (Points X) ℤ)
    (z : Points (zeroScheme L s).X) :
    cycle pX δ L s k α z =
      ∑ᶠ x : Points X,
        (if Hom.relativeDimensionFunction pX δ x = k + 1 then
          α x • generator pX δ L s k x else 0) z := rfl

/-- Refined intersection of a singleton cycle is its point-closure generator. -/
theorem cycle_pointCycle (k : ℤ) (x : Points X)
    (hx : Hom.relativeDimensionFunction pX δ x = k + 1) :
    cycle pX δ L s k (Hom.pointCycle x) = generator pX δ L s k x := by
  classical
  ext z
  change (∑ᶠ y : Points X,
    (if Hom.relativeDimensionFunction pX δ y = k + 1 then
      Hom.pointCycle x y • generator pX δ L s k y else 0) z) = _
  rw [finsum_eq_single _ x]
  · simp [Hom.pointCycle, hx, Function.locallyFinsuppWithin.single_apply]
  · intro y hy
    by_cases hdegree : Hom.relativeDimensionFunction pX δ y = k + 1
    · simp [hdegree, Hom.pointCycle, Function.locallyFinsuppWithin.single_apply, hy]
    · simp [hdegree]

/-- Refined intersection lowers cycle degree by one. -/
theorem cycle_mem (k : ℤ) (α : Hom.cycleGroup pX δ (k + 1)) :
    cycle pX δ L s k α ∈ Hom.cycleGroup (zeroSchemeι L s ≫ pX) δ k := sorry

/-- Refined intersection of the zero cycle is zero. -/
theorem cycle_zero (k : ℤ) : cycle pX δ L s k 0 = 0 := sorry

/-- Refined intersection is additive on cycles. -/
theorem cycle_add (k : ℤ) (α β : Function.locallyFinsupp (Points X) ℤ) :
    cycle pX δ L s k (α + β) =
      cycle pX δ L s k α + cycle pX δ L s k β := sorry

/-- The degree-supported additive refined intersection map on cycles. -/
def cycleHom (k : ℤ) :
    Hom.cycleGroup pX δ (k + 1) →+ Hom.cycleGroup (zeroSchemeι L s ≫ pX) δ k where
  toFun α := ⟨cycle pX δ L s k α, cycle_mem pX δ L s k α⟩
  map_zero' := Subtype.ext (cycle_zero pX δ L s k)
  map_add' α β := Subtype.ext (cycle_add pX δ L s k α β)

/-- Refined intersection sends rational boundaries to rational boundaries. -/
theorem mem_boundaries (k : ℤ) :
    RationalEquivalence.boundaries pX δ (k + 1) ≤
      (RationalEquivalence.boundaries (zeroSchemeι L s ≫ pX) δ k).comap
        (cycleHom pX δ L s k) := sorry

/-- Refined Gysin on Chow groups is induced by the explicit cycle intersection. -/
def gysin (k : ℤ) :
    Hom.chowGroup pX δ (k + 1) →+ Hom.chowGroup (zeroSchemeι L s ≫ pX) δ k :=
  QuotientAddGroup.map
    (RationalEquivalence.boundaries pX δ (k + 1))
    (RationalEquivalence.boundaries (zeroSchemeι L s ≫ pX) δ k)
    (cycleHom pX δ L s k) (mem_boundaries pX δ L s k)

/-- Refined Gysin sends the class of a cycle to the class of its refined intersection. -/
theorem gysin_mk (k : ℤ) (α : Hom.cycleGroup pX δ (k + 1)) :
    gysin pX δ L s k (Hom.chowMk pX δ (k + 1) α) =
      Hom.chowMk (zeroSchemeι L s ≫ pX) δ k (cycleHom pX δ L s k α) := sorry

end AlgebraicGeometry.AlgebraicSpace.ChowGroup.RefinedGysin

namespace AlgebraicGeometry.AlgebraicSpace.Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
  (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
  (δ : Points B → ℤ) [IsDimensionFunction δ] (k : ℤ)
  (L : X.Modules) [isInvertibleObject L] (s : L.sections)

/-- The induced closed immersion of a point closure contained in the zero scheme. -/
def gysinContainedImmersion (x : Points X) (hx : x ∈ (zeroScheme L s).pointsSet) :
    PointClosure.space x ⟶ (zeroScheme L s).X :=
  IntersectionTheory.ZeroSchemeFactor.lift L s (PointClosure.ι x)
    ((ChowGroup.RefinedGysin.contained_iff_mem L s x).mpr hx)

/-- The induced immersion into the zero scheme factors the point-closure immersion. -/
theorem gysinContainedImmersion_comp (x : Points X)
    (hx : x ∈ (zeroScheme L s).pointsSet) :
    gysinContainedImmersion L s x hx ≫ zeroSchemeι L s = PointClosure.ι x :=
  IntersectionTheory.ZeroSchemeFactor.lift_ι L s (PointClosure.ι x) _

/-- The induced map from a contained point closure to the zero scheme is closed. -/
instance instIsClosedImmersion_gysinContainedImmersion (x : Points X)
    (hx : x ∈ (zeroScheme L s).pointsSet) :
    IsClosedImmersion (gysinContainedImmersion L s x hx) :=
  IntersectionTheory.ZeroSchemeFactor.lift_isClosedImmersion L s (PointClosure.ι x) _

/-- Refined intersection sends cycles of degree `k + 1` to Chow classes of
degree `k` on the zero scheme of the section. -/
def gysin : cycleGroup f δ (k + 1) →+ chowGroup (zeroSchemeι L s ≫ f) δ k :=
  (chowMk (zeroSchemeι L s ≫ f) δ k).comp
    (ChowGroup.RefinedGysin.cycleHom f δ L s k)

/-- Refined Gysin is the Chow class of the locally finite intersection cycle. -/
theorem gysin_apply (α : cycleGroup f δ (k + 1)) :
    gysin f δ k L s α =
      chowMk (zeroSchemeι L s ≫ f) δ k (ChowGroup.RefinedGysin.cycleHom f δ L s k α) :=
  rfl

/-- The Gysin value of a point outside the zero scheme is the class of its
multiplicity-weighted intersection cycle. -/
theorem gysin_point_of_not_mem (x : Points X)
    (hx : relativeDimensionFunction f δ x = k + 1)
    (hmem : x ∉ (zeroScheme L s).pointsSet) :
    gysin f δ k L s ⟨pointCycle x, pointCycle_mem f δ k x hx⟩ =
      chowMk (zeroSchemeι L s ≫ f) δ k
        ⟨gysinIntersectionCycle f δ k L s x, gysinIntersectionCycle_mem f δ k L s x⟩ := by
  change chowMk (zeroSchemeι L s ≫ f) δ k
    (ChowGroup.RefinedGysin.cycleHom f δ L s k _) = _
  congr 1
  apply Subtype.ext
  change ChowGroup.RefinedGysin.cycle f δ L s k (pointCycle x) = _
  rw [ChowGroup.RefinedGysin.cycle_pointCycle f δ L s k x hx]
  exact ChowGroup.RefinedGysin.generator_of_not_mem f δ L s k x hmem

/-- For a point closure contained in the zero scheme, refined Gysin is the
pushforward of the restricted first Chern class capped with its fundamental cycle. -/
theorem gysin_point_eq_pushforward_firstChern (x : Points X)
    (hx : relativeDimensionFunction f δ x = k + 1)
    (hmem : x ∈ (zeroScheme L s).pointsSet) :
    gysin f δ k L s ⟨pointCycle x, pointCycle_mem f δ k x hx⟩ =
      ChowGroup.properPushforward (PointClosure.ι x ≫ f) (zeroSchemeι L s ≫ f) δ
        (gysinContainedImmersion L s x hmem)
        (by rw [← Category.assoc, gysinContainedImmersion_comp]) k
        (@firstChernClassCap S B (PointClosure.space x) inferInstance inferInstance
          (PointClosure.ι x ≫ f) (closure_quasiSeparated f x)
          (closure_locallyOfFiniteType f x) δ inferInstance
          ((Modules.pullback (PointClosure.ι x)).obj L)
          (Modules.isInvertibleObject_pullback (PointClosure.ι x) L) k
          (ChowGroup.RefinedGysin.fundamental f δ k x hx)) := sorry

/-- Intersection with an effective Cartier zero divisor is the closed
pushforward of its refined Gysin homomorphism. -/
def cartierIntersection [IsEffectiveCartierDivisor (zeroSchemeι L s)] :
    cycleGroup f δ (k + 1) →+ chowGroup f δ k :=
  (chowPushforward f δ (zeroScheme L s) k).comp (gysin f δ k L s)

/-- Effective Cartier intersection is the pushforward of refined Gysin. -/
theorem cartierIntersection_eq [IsEffectiveCartierDivisor (zeroSchemeι L s)]
    (α : cycleGroup f δ (k + 1)) :
    cartierIntersection f δ k L s α =
      chowPushforward f δ (zeroScheme L s) k (gysin f δ k L s α) := rfl

end AlgebraicGeometry.AlgebraicSpace.Hom
