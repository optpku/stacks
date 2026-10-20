/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.WeilDivisor
public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin
public import ReasLib.AlgebraicGeometry.ChowGroup.Supported
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.PullbackStalk
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure.GenericPoint
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Pseudo
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.MeromorphicSection.GenericGerm
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Intersection of pseudo-divisors with supported Chow classes

This file defines pseudo-divisor intersection first on cycles and then on Chow classes carrying
an explicit closed support. It also compares the construction for a global section with the
zero-scheme Gysin homomorphism.
-/

@[expose] public section

open CategoryTheory Function Opposite Set Topology
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PseudoDivisor

/-- The germ of the complement section of `D` at a point outside its support. -/
noncomputable def complementGerm {X : Scheme.{u}} (D : PseudoDivisor X)
    (x : X) (hx : x ∉ D.support) : RingedSpace.stalkModuleCat D.lineBundle x :=
  ((Scheme.Modules.restrictStalkNatIso (Scheme.Opens.ι D.support.compl)
      (⟨x, hx⟩ : D.support.compl)).hom.app D.lineBundle)
    (TopCat.Presheaf.Γgerm
      (Scheme.Modules.restrict D.lineBundle (Scheme.Opens.ι D.support.compl)).val.presheaf
      (⟨x, hx⟩ : D.support.compl) (D.section_.1 (op ⊤)))

/-- The complement germ transported to the image of the generic point of the reduced point
closure. -/
noncomputable def complementGermAtPointClosureGeneric {X : Scheme.{u}}
    (D : PseudoDivisor X) (x : X) (hx : x ∉ D.support) :
    RingedSpace.stalkModuleCat D.lineBundle
      ((Scheme.PointClosure.ι x).base (genericPoint (Scheme.PointClosure.scheme x))) :=
  (Scheme.PointClosure.ι_map_genericPoint x).symm ▸ complementGerm D x hx

/-- Pull the complement germ to the generic stalk of the reduced closure of `x`. -/
noncomputable def pointClosureGenericGerm {X : Scheme.{u}} (D : PseudoDivisor X)
    (x : X) (hx : x ∉ D.support) :
    RingedSpace.stalkModuleCat
      ((Scheme.Modules.pullback (Scheme.PointClosure.ι x)).obj D.lineBundle)
      (genericPoint (Scheme.PointClosure.scheme x)) :=
  @RingedSpace.Hom.pullbackStalkUnitHom
    (Scheme.PointClosure.scheme x).toRingedSpace X.toRingedSpace
    (Scheme.PointClosure.ι x).toLRSHom.toShHom D.lineBundle
    (genericPoint (Scheme.PointClosure.scheme x))
    (complementGermAtPointClosureGeneric D x hx)

/-- The meromorphic section on the reduced closure of `x` induced by the complement section
of `D`. -/
noncomputable def pointClosureMeromorphicSection {X : Scheme.{u}} (D : PseudoDivisor X)
    (x : X) (hx : x ∉ D.support) :
    (Scheme.PointClosure.scheme x).toLocallyRingedSpace.meromorphicSections
      ((Scheme.Modules.pullback (Scheme.PointClosure.ι x)).obj D.lineBundle) :=
  @Scheme.Modules.meromorphicSectionOfGenericGerm
    (Scheme.PointClosure.scheme x) inferInstance
    ((Scheme.Modules.pullback (Scheme.PointClosure.ι x)).obj D.lineBundle)
    (Scheme.Modules.Invertible.pullback (Scheme.PointClosure.ι x) D.invertible)
    (pointClosureGenericGerm D x hx)

/-- The generic germ of the induced meromorphic section is the canonical meromorphic-stalk
image of the germ pulled back from `D.section_` on the complement of `D.support`. -/
theorem pointClosureMeromorphicSection_genericGerm {X : Scheme.{u}}
    (D : PseudoDivisor X) (x : X) (hx : x ∉ D.support) :
    SheafOfModules.sectionGermOfCommRing (pointClosureMeromorphicSection D x hx)
        (genericPoint (Scheme.PointClosure.scheme x)) =
      (Scheme.PointClosure.scheme x).toLocallyRingedSpace.meromorphicSectionStalkMap
        ((Scheme.Modules.pullback (Scheme.PointClosure.ι x)).obj D.lineBundle)
        (genericPoint (Scheme.PointClosure.scheme x))
        (pointClosureGenericGerm D x hx) := sorry

/-- The meromorphic section induced on a point closure from a nowhere-vanishing complement
section is nonzero. -/
theorem pointClosureMeromorphicSection_ne_zero {X : Scheme.{u}} (D : PseudoDivisor X)
    (x : X) (hx : x ∉ D.support) :
    pointClosureMeromorphicSection D x hx ≠ 0 := sorry

/-- The divisor of the induced meromorphic section on a point closure has degree one less than
the point. -/
theorem pointClosureDivisorCycle_mem {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (D : PseudoDivisor X)
    (k : ℤ) (x : X) (hx : x ∉ D.support)
    (hdim : p.relativeDimensionFunction δ x = k + 1) :
    @Scheme.nonzeroMeromorphicSectionDivisorCycle (Scheme.PointClosure.scheme x)
        (@Scheme.PointClosure.scheme_isLocallyNoetherian X
          (LocallyOfFiniteType.isLocallyNoetherian p) x) inferInstance
        ((Scheme.Modules.pullback (Scheme.PointClosure.ι x)).obj D.lineBundle)
        (Scheme.Modules.Invertible.pullback (Scheme.PointClosure.ι x) D.invertible)
        (pointClosureMeromorphicSection D x hx)
        (pointClosureMeromorphicSection_ne_zero D x hx) ∈
      AlgebraicCycle.dimensionSubgroup
        ((Scheme.PointClosure.ι x ≫ p).relativeDimensionFunction δ) k := sorry

/-- The degree-`k` divisor cycle on the reduced closure of a point outside the support of
`D`. -/
noncomputable def pointClosureDivisorCycle {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (D : PseudoDivisor X)
    (k : ℤ) (x : X) (hx : x ∉ D.support)
    (hdim : p.relativeDimensionFunction δ x = k + 1) :
    CycleGroup (Scheme.PointClosure.scheme x)
      ((Scheme.PointClosure.ι x ≫ p).relativeDimensionFunction δ) k :=
  ⟨@Scheme.nonzeroMeromorphicSectionDivisorCycle (Scheme.PointClosure.scheme x)
      (@Scheme.PointClosure.scheme_isLocallyNoetherian X
        (LocallyOfFiniteType.isLocallyNoetherian p) x) inferInstance
      ((Scheme.Modules.pullback (Scheme.PointClosure.ι x)).obj D.lineBundle)
      (Scheme.Modules.Invertible.pullback (Scheme.PointClosure.ι x) D.invertible)
      (pointClosureMeromorphicSection D x hx)
      (pointClosureMeromorphicSection_ne_zero D x hx),
    pointClosureDivisorCycle_mem p δ D k x hx hdim⟩

/-- The cycle contributed by a degree-`k + 1` point: first-Chern intersection on the support
of `D`, and the divisor of the complement section off that support. -/
noncomputable def intersectionGeneratorCycle {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (D : PseudoDivisor X)
    (k : ℤ) (x : X) (hx : p.relativeDimensionFunction δ x = k + 1) :
    CycleGroup X (p.relativeDimensionFunction δ) k :=
  @dite _ (x ∈ D.support) (Classical.propDecidable _)
    (fun _ ↦
      @Scheme.Modules.firstChernGeneratorCycle X
        (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance D.lineBundle D.invertible k x hx)
    (fun hmem ↦
      CycleGroup.mapHom (Scheme.PointClosure.ι x)
        ((Scheme.PointClosure.ι x ≫ p).relativeDimensionFunction δ)
        (p.relativeDimensionFunction δ) k
        (pointClosureDivisorCycle p δ D k x hmem hx))

/-- The coefficient-weighted pseudo-divisor generator cycles of a supported cycle form a
locally finite family. -/
theorem intersectionGeneratorTermsLocallyFinite {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (D : PseudoDivisor X)
    (T : TopologicalSpace.Closeds X) (k : ℤ) (α : CycleGroup.onClosed p δ T (k + 1)) :
    LocallyFinite fun x : X ↦
      (CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) k
        (if hx : p.relativeDimensionFunction δ x = k + 1 then
          (CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) (k + 1)
            (CycleGroup.onClosedPushforward p δ T (k + 1) α) x) •
              intersectionGeneratorCycle p δ D k x hx
        else 0)).support := sorry

/-- The explicit ambient cycle obtained by extending pseudo-divisor intersection from
degree-`k + 1` point generators. -/
noncomputable def ambientIntersectionCycle {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (D : PseudoDivisor X)
    (T : TopologicalSpace.Closeds X) (k : ℤ)
    (α : CycleGroup.onClosed p δ T (k + 1)) : CycleGroup X (p.relativeDimensionFunction δ) k :=
  CycleGroup.locallyFiniteSum (p.relativeDimensionFunction δ) k
    (fun x : X ↦
      if hx : p.relativeDimensionFunction δ x = k + 1 then
        (CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) (k + 1)
          (CycleGroup.onClosedPushforward p δ T (k + 1) α) x) •
            intersectionGeneratorCycle p δ D k x hx
      else 0)
    (intersectionGeneratorTermsLocallyFinite p δ D T k α)

/-- The ambient pseudo-divisor intersection cycle is supported on `D.support ∩ T`. -/
theorem ambientIntersectionCycle_support {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (D : PseudoDivisor X)
    (T : TopologicalSpace.Closeds X) (k : ℤ) (α : CycleGroup.onClosed p δ T (k + 1)) :
    (CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) k
      (ambientIntersectionCycle p δ D T k α)).support ⊆ (D.support ⊓ T : Set X) := sorry

/-- The ambient pseudo-divisor intersection cycle sends zero to zero. -/
theorem ambientIntersectionCycle_zero {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (D : PseudoDivisor X)
    (T : TopologicalSpace.Closeds X) (k : ℤ) :
    ambientIntersectionCycle p δ D T k 0 = 0 := sorry

/-- The ambient pseudo-divisor intersection cycle preserves addition. -/
theorem ambientIntersectionCycle_add {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (D : PseudoDivisor X)
    (T : TopologicalSpace.Closeds X) (k : ℤ)
    (α β : CycleGroup.onClosed p δ T (k + 1)) :
    ambientIntersectionCycle p δ D T k (α + β) =
      ambientIntersectionCycle p δ D T k α + ambientIntersectionCycle p δ D T k β := sorry

/-- The additive ambient cycle map underlying pseudo-divisor intersection. -/
noncomputable def ambientIntersectionCycleHom {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (D : PseudoDivisor X)
    (T : TopologicalSpace.Closeds X) (k : ℤ) :
    CycleGroup.onClosed p δ T (k + 1) →+ CycleGroup X (p.relativeDimensionFunction δ) k where
  toFun := ambientIntersectionCycle p δ D T k
  map_zero' := ambientIntersectionCycle_zero p δ D T k
  map_add' := ambientIntersectionCycle_add p δ D T k

/-- The concrete pseudo-divisor intersection map on cycles, with target on
`D.support ∩ T`. -/
noncomputable def intersectionCycle {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (D : PseudoDivisor X)
    (T : TopologicalSpace.Closeds X) (k : ℤ) :
    CycleGroup.onClosed p δ T (k + 1) →+
      CycleGroup.onClosed p δ (D.support ⊓ T) k :=
  (CycleGroup.restrictToClosedHom p δ (D.support ⊓ T) k).comp
    (ambientIntersectionCycleHom p δ D T k)

/-- Every point in the support of the cycle `D · α` maps into `D.support ∩ T`. -/
theorem intersectionCycle_support {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (D : PseudoDivisor X)
    (T : TopologicalSpace.Closeds X) (k : ℤ) (α : CycleGroup.onClosed p δ T (k + 1)) :
    Set.MapsTo (Scheme.IdealSheafData.vanishingIdeal (D.support ⊓ T)).subschemeι
      (CycleGroup.toAlgebraicCycle
        (((Scheme.IdealSheafData.vanishingIdeal (D.support ⊓ T)).subschemeι ≫ p).relativeDimensionFunction δ)
        k (intersectionCycle p δ D T k α)).support
      (D.support ⊓ T : Set X) := sorry

/-- Pseudo-divisor intersection sends rational boundaries to rational boundaries. -/
theorem intersectionCycle_mem_boundaries {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (D : PseudoDivisor X)
    (T : TopologicalSpace.Closeds X) (k : ℤ) :
    @RationalEquivalence.boundaries
        (Scheme.IdealSheafData.vanishingIdeal T).subscheme
        (@Scheme.IdealSheafData.subschemeIsLocallyNoetherian X
          (LocallyOfFiniteType.isLocallyNoetherian p)
          (Scheme.IdealSheafData.vanishingIdeal T))
        (((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ p).relativeDimensionFunction δ)
        inferInstance (k + 1) ≤
      (@RationalEquivalence.boundaries
        (Scheme.IdealSheafData.vanishingIdeal (D.support ⊓ T)).subscheme
        (@Scheme.IdealSheafData.subschemeIsLocallyNoetherian X
          (LocallyOfFiniteType.isLocallyNoetherian p)
          (Scheme.IdealSheafData.vanishingIdeal (D.support ⊓ T)))
        (((Scheme.IdealSheafData.vanishingIdeal (D.support ⊓ T)).subschemeι ≫ p).relativeDimensionFunction δ)
        inferInstance k).comap
        (intersectionCycle p δ D T k) := sorry

/-- Intersection with `D` lowers Chow degree by one and is supported on
`D.support ∩ T`. -/
noncomputable def intersection {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (D : PseudoDivisor X)
    (T : TopologicalSpace.Closeds X) (k : ℤ) :
    ChowGroup.onClosed p δ T (k + 1) →+ ChowGroup.onClosed p δ (D.support ⊓ T) k :=
  QuotientAddGroup.map
    (@RationalEquivalence.boundaries
      (Scheme.IdealSheafData.vanishingIdeal T).subscheme
      (@Scheme.IdealSheafData.subschemeIsLocallyNoetherian X
        (LocallyOfFiniteType.isLocallyNoetherian p)
        (Scheme.IdealSheafData.vanishingIdeal T))
      (((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ p).relativeDimensionFunction δ)
      inferInstance (k + 1))
    (@RationalEquivalence.boundaries
      (Scheme.IdealSheafData.vanishingIdeal (D.support ⊓ T)).subscheme
      (@Scheme.IdealSheafData.subschemeIsLocallyNoetherian X
        (LocallyOfFiniteType.isLocallyNoetherian p)
        (Scheme.IdealSheafData.vanishingIdeal (D.support ⊓ T)))
      (((Scheme.IdealSheafData.vanishingIdeal (D.support ⊓ T)).subschemeι ≫ p).relativeDimensionFunction δ)
      inferInstance k)
    (intersectionCycle p δ D T k) (intersectionCycle_mem_boundaries p δ D T k)

/-- Pseudo-divisor intersection on a Chow class is represented by the explicit cycle-level
intersection. -/
theorem intersection_chowClass {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (D : PseudoDivisor X)
    (T : TopologicalSpace.Closeds X) (k : ℤ) (α : CycleGroup.onClosed p δ T (k + 1)) :
    intersection p δ D T k
        (@chowClass (Scheme.IdealSheafData.vanishingIdeal T).subscheme
          (@Scheme.IdealSheafData.subschemeIsLocallyNoetherian X
            (LocallyOfFiniteType.isLocallyNoetherian p)
            (Scheme.IdealSheafData.vanishingIdeal T))
          (((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ p).relativeDimensionFunction δ)
          inferInstance (k + 1) α) =
      @chowClass (Scheme.IdealSheafData.vanishingIdeal (D.support ⊓ T)).subscheme
        (@Scheme.IdealSheafData.subschemeIsLocallyNoetherian X
          (LocallyOfFiniteType.isLocallyNoetherian p)
          (Scheme.IdealSheafData.vanishingIdeal (D.support ⊓ T)))
        (((Scheme.IdealSheafData.vanishingIdeal (D.support ⊓ T)).subschemeι ≫ p).relativeDimensionFunction δ)
        inferInstance k
        (intersectionCycle p δ D T k α) := sorry

/-- Intersect an ambient Chow class presented with explicit closed support by a pseudo-divisor.
The resulting supported class has support `D.support ∩ α.support`. -/
noncomputable def intersectionSupported {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (D : PseudoDivisor X) (k : ℤ)
    (α : ChowGroup.Supported p δ (k + 1)) : ChowGroup.Supported p δ k :=
  ChowGroup.Supported.ofClosed p δ (D.support ⊓ α.support) k
    (intersection p δ D α.support k α.class_)

/-- Supported pseudo-divisor intersection records the expected intersected support and the
supported Chow class produced by `intersection`. -/
theorem intersectionSupported_spec {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (D : PseudoDivisor X) (k : ℤ)
    (α : ChowGroup.Supported p δ (k + 1)) :
    (intersectionSupported p δ D k α).support = D.support ⊓ α.support ∧
      (intersectionSupported p δ D k α).class_ =
        intersection p δ D α.support k α.class_ := sorry

/-- Proper pushforward identifies the ambient view of supported pseudo-divisor intersection
with the pushforward of its support-refined Chow class. -/
theorem intersectionSupported_toAmbient {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (D : PseudoDivisor X) (k : ℤ)
    (α : ChowGroup.Supported p δ (k + 1)) :
    (intersectionSupported p δ D k α).toAmbient =
      ChowGroup.onClosedPushforward p δ (D.support ⊓ α.support) k
        (intersection p δ D α.support k α.class_) := sorry

/-- For the pseudo-divisor of a global section, supported intersection agrees after ambient
pushforward with the Gysin construction for that section. -/
theorem ofGlobalSection_intersection_pushforward {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (lineBundle : X.Modules)
    [Scheme.Modules.Invertible lineBundle] (section_ : lineBundle.sections)
    (T : TopologicalSpace.Closeds X) (k : ℤ)
    (α : CycleGroup.onClosed p δ T (k + 1)) :
    ChowGroup.onClosedPushforward p δ
        ((ofGlobalSection lineBundle section_).support ⊓ T) k
        (intersection p δ (ofGlobalSection lineBundle section_) T k
          (@chowClass (Scheme.IdealSheafData.vanishingIdeal T).subscheme
            (@Scheme.IdealSheafData.subschemeIsLocallyNoetherian X
              (LocallyOfFiniteType.isLocallyNoetherian p)
              (Scheme.IdealSheafData.vanishingIdeal T))
            (((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ p).relativeDimensionFunction δ)
            inferInstance (k + 1) α)) =
      ChowGroup.map δ (Over.mk (Scheme.zeroSchemeι lineBundle section_ ≫ p)) (Over.mk p)
        (Over.homMk (Scheme.zeroSchemeι lineBundle section_)) k
        (Scheme.Modules.gysin p δ lineBundle section_ k
          (CycleGroup.onClosedPushforward p δ T (k + 1) α)) := sorry

end AlgebraicGeometry.Scheme.PseudoDivisor
