/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.LocallyPrincipal
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ZeroScheme
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.VirtualNormalBundle.IdealSurjection
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback

/-!
# Gysin homomorphisms from ideal-sheaf quotients

A locally principal closed subscheme equipped with an invertible module and a quotient of its
pulled-back ideal sheaf carries an explicit degree-lowering Gysin homomorphism.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Function Set Topology
open Scheme.Hom.VirtualNormalBundle

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The scheme-theoretic intersection of a closed subscheme with the reduced closure of a
point. -/
noncomputable def pointIntersection {X : Scheme.{u}} (D : X.IdealSheafData) (x : X) :
    X.IdealSheafData :=
  D ⊔ (Scheme.PointClosure.reducedStructure x).ideal

/-- The point intersection is cut out by the sum of the two defining ideals. -/
theorem pointIntersection_def {X : Scheme.{u}} (D : X.IdealSheafData) (x : X) :
    D.pointIntersection x = D ⊔ (Scheme.PointClosure.reducedStructure x).ideal := sorry

/-- The canonical closed immersion from the point intersection to `D`. -/
@[reducible]
noncomputable def pointIntersectionToSubscheme {X : Scheme.{u}}
    (D : X.IdealSheafData) (x : X) : (D.pointIntersection x).subscheme ⟶ D.subscheme :=
  inclusion le_sup_left

/-- The point-intersection inclusion followed by `D.subschemeι` is its ambient inclusion. -/
theorem pointIntersectionToSubscheme_comp {X : Scheme.{u}}
    (D : X.IdealSheafData) (x : X) :
    D.pointIntersectionToSubscheme x ≫ D.subschemeι =
      (D.pointIntersection x).subschemeι := sorry

/-- A point of `D` makes the ideal of `D` vanish on its reduced closure. -/
theorem le_pointClosureKer {X : Scheme.{u}} (D : X.IdealSheafData) (x : X)
    (hx : x ∈ D.support) : D ≤ (Scheme.PointClosure.ι x).ker := sorry

/-- The canonical morphism from a contained reduced point closure to `D`. -/
noncomputable def pointClosureToSubscheme {X : Scheme.{u}}
    (D : X.IdealSheafData) (x : X) (hx : x ∈ D.support) :
    Scheme.PointClosure.scheme x ⟶ D.subscheme :=
  D.lift (Scheme.PointClosure.ι x) (D.le_pointClosureKer x hx)

/-- The contained point-closure map followed by `D.subschemeι` is the ambient inclusion. -/
theorem pointClosureToSubscheme_comp {X : Scheme.{u}}
    (D : X.IdealSheafData) (x : X) (hx : x ∈ D.support) :
    D.pointClosureToSubscheme x hx ≫ D.subschemeι = Scheme.PointClosure.ι x := sorry

/-- The contained point-closure map to `D` is a closed immersion. -/
instance pointClosureToSubscheme_isClosedImmersion {X : Scheme.{u}}
    (D : X.IdealSheafData) (x : X) (hx : x ∈ D.support) :
    IsClosedImmersion (D.pointClosureToSubscheme x hx) := sorry

/-- Off `D`, the fundamental cycle of the scheme-theoretic point intersection has the
expected degree. -/
theorem pointIntersectionFundamental_mem
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (delta : S → ℤ) [IsDimensionFunction delta] (D : X.IdealSheafData)
    [IsLocallyPrincipalClosedSubscheme D.subschemeι] (k : ℤ) (x : X)
    (hx : p.relativeDimensionFunction delta x = k + 1) (hmem : x ∉ D.support) :
    @AlgebraicCycle.fundamental (D.pointIntersection x).subscheme
        (@subschemeIsLocallyNoetherian X (LocallyOfFiniteType.isLocallyNoetherian p)
          (D.pointIntersection x))
        (((D.pointIntersection x).subschemeι ≫ p).relativeDimensionFunction delta) k ∈
      AlgebraicCycle.dimensionSubgroup
        (((D.pointIntersection x).subschemeι ≫ p).relativeDimensionFunction delta) k := sorry

/-- The degree-`k` fundamental cycle of the intersection of `D` with a reduced point closure. -/
noncomputable def pointIntersectionFundamentalCycle
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (delta : S → ℤ) [IsDimensionFunction delta] (D : X.IdealSheafData)
    [IsLocallyPrincipalClosedSubscheme D.subschemeι] (k : ℤ) (x : X)
    (hx : p.relativeDimensionFunction delta x = k + 1) (hmem : x ∉ D.support) :
    CycleGroup (D.pointIntersection x).subscheme
      (((D.pointIntersection x).subschemeι ≫ p).relativeDimensionFunction delta) k :=
  ⟨@AlgebraicCycle.fundamental (D.pointIntersection x).subscheme
      (@subschemeIsLocallyNoetherian X (LocallyOfFiniteType.isLocallyNoetherian p)
        (D.pointIntersection x))
      (((D.pointIntersection x).subschemeι ≫ p).relativeDimensionFunction delta) k,
    pointIntersectionFundamental_mem p delta D k x hx hmem⟩

/-- Forgetting the grading of the point-intersection fundamental cycle recovers its
underlying fundamental algebraic cycle. -/
theorem pointIntersectionFundamentalCycle_toAlgebraicCycle
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (delta : S → ℤ) [IsDimensionFunction delta] (D : X.IdealSheafData)
    [IsLocallyPrincipalClosedSubscheme D.subschemeι] (k : ℤ) (x : X)
    (hx : p.relativeDimensionFunction delta x = k + 1) (hmem : x ∉ D.support) :
    CycleGroup.toAlgebraicCycle
        (((D.pointIntersection x).subschemeι ≫ p).relativeDimensionFunction delta) k
        (D.pointIntersectionFundamentalCycle p delta k x hx hmem) =
      @AlgebraicCycle.fundamental (D.pointIntersection x).subscheme
        (@subschemeIsLocallyNoetherian X (LocallyOfFiniteType.isLocallyNoetherian p)
          (D.pointIntersection x))
        (((D.pointIntersection x).subschemeι ≫ p).relativeDimensionFunction delta) k := sorry

/-- The generalized rank-one Gysin contribution of a point: use `c₁(N)` on components
contained in `D`, and the scheme-theoretic intersection cycle otherwise. -/
noncomputable def gysinGeneratorCycle
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (delta : S → ℤ) [IsDimensionFunction delta] (D : X.IdealSheafData)
    [IsLocallyPrincipalClosedSubscheme D.subschemeι]
    (N : D.subscheme.Modules) [Scheme.Modules.Invertible N]
    (sigma : Scheme.Modules.dual N ⟶
      (Scheme.Modules.pullback D.subschemeι).obj
        (RingedSpace.Hom.kernelIdealSheaf D.subschemeι.toShHom))
    [Epi sigma] (k : ℤ) (x : X) (hx : p.relativeDimensionFunction delta x = k + 1) :
    CycleGroup D.subscheme ((D.subschemeι ≫ p).relativeDimensionFunction delta) k :=
  @dite _ (x ∈ D.support) (Classical.propDecidable _)
    (fun hmem ↦
      CycleGroup.mapHom (D.pointClosureToSubscheme x hmem)
        ((Scheme.PointClosure.ι x ≫ p).relativeDimensionFunction delta)
        ((D.subschemeι ≫ p).relativeDimensionFunction delta) k
        (@Scheme.Modules.firstChernCycle (Scheme.PointClosure.scheme x)
          (@Scheme.PointClosure.scheme_isLocallyNoetherian X
            (LocallyOfFiniteType.isLocallyNoetherian p) x)
          ((Scheme.PointClosure.ι x ≫ p).relativeDimensionFunction delta) inferInstance
          ((Scheme.Modules.pullback (D.pointClosureToSubscheme x hmem)).obj N)
          inferInstance k (Scheme.Modules.pointClosureFundamentalCycle p delta k x hx)))
    (fun hmem ↦
      CycleGroup.mapHom (D.pointIntersectionToSubscheme x)
        (((D.pointIntersection x).subschemeι ≫ p).relativeDimensionFunction delta)
        ((D.subschemeι ≫ p).relativeDimensionFunction delta) k
        (D.pointIntersectionFundamentalCycle p delta k x hx hmem))

/-- On `D`, the generalized Gysin generator is the pushforward of first-Chern intersection
with the fundamental cycle of the reduced point closure. -/
theorem gysinGeneratorCycle_of_mem
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (delta : S → ℤ) [IsDimensionFunction delta] (D : X.IdealSheafData)
    [IsLocallyPrincipalClosedSubscheme D.subschemeι]
    (N : D.subscheme.Modules) [Scheme.Modules.Invertible N]
    (sigma : Scheme.Modules.dual N ⟶
      (Scheme.Modules.pullback D.subschemeι).obj
        (RingedSpace.Hom.kernelIdealSheaf D.subschemeι.toShHom))
    [Epi sigma] (k : ℤ) (x : X) (hx : p.relativeDimensionFunction delta x = k + 1)
    (hmem : x ∈ D.support) :
    gysinGeneratorCycle p delta D N sigma k x hx =
      CycleGroup.mapHom (D.pointClosureToSubscheme x hmem)
        ((Scheme.PointClosure.ι x ≫ p).relativeDimensionFunction delta)
        ((D.subschemeι ≫ p).relativeDimensionFunction delta) k
        (@Scheme.Modules.firstChernCycle (Scheme.PointClosure.scheme x)
          (@Scheme.PointClosure.scheme_isLocallyNoetherian X
            (LocallyOfFiniteType.isLocallyNoetherian p) x)
          ((Scheme.PointClosure.ι x ≫ p).relativeDimensionFunction delta) inferInstance
          ((Scheme.Modules.pullback (D.pointClosureToSubscheme x hmem)).obj N)
          inferInstance k (Scheme.Modules.pointClosureFundamentalCycle p delta k x hx)) := sorry

/-- Off `D`, the generalized Gysin generator is the pushed-forward fundamental cycle of the
scheme-theoretic intersection with the reduced point closure. -/
theorem gysinGeneratorCycle_of_not_mem
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (delta : S → ℤ) [IsDimensionFunction delta] (D : X.IdealSheafData)
    [IsLocallyPrincipalClosedSubscheme D.subschemeι]
    (N : D.subscheme.Modules) [Scheme.Modules.Invertible N]
    (sigma : Scheme.Modules.dual N ⟶
      (Scheme.Modules.pullback D.subschemeι).obj
        (RingedSpace.Hom.kernelIdealSheaf D.subschemeι.toShHom))
    [Epi sigma] (k : ℤ) (x : X) (hx : p.relativeDimensionFunction delta x = k + 1)
    (hmem : x ∉ D.support) :
    gysinGeneratorCycle p delta D N sigma k x hx =
      CycleGroup.mapHom (D.pointIntersectionToSubscheme x)
        (((D.pointIntersection x).subschemeι ≫ p).relativeDimensionFunction delta)
        ((D.subschemeι ≫ p).relativeDimensionFunction delta) k
        (D.pointIntersectionFundamentalCycle p delta k x hx hmem) := sorry

/-- Generalized rank-one Gysin generator cycles form a locally finite family on `D`. -/
theorem gysinGeneratorTermsLocallyFinite
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (delta : S → ℤ) [IsDimensionFunction delta] (D : X.IdealSheafData)
    [IsLocallyPrincipalClosedSubscheme D.subschemeι]
    (N : D.subscheme.Modules) [Scheme.Modules.Invertible N]
    (sigma : Scheme.Modules.dual N ⟶
      (Scheme.Modules.pullback D.subschemeι).obj
        (RingedSpace.Hom.kernelIdealSheaf D.subschemeι.toShHom))
    [Epi sigma] (k : ℤ) (alpha : CycleGroup X (p.relativeDimensionFunction delta) (k + 1)) :
    LocallyFinite fun x : X ↦
      (CycleGroup.toAlgebraicCycle ((D.subschemeι ≫ p).relativeDimensionFunction delta) k
        (if hx : p.relativeDimensionFunction delta x = k + 1 then
          (CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction delta) (k + 1) alpha x) •
            gysinGeneratorCycle p delta D N sigma k x hx
        else 0)).support := sorry

/-- The explicit generalized Gysin cycle obtained by extending the point-generator formula
linearly. -/
noncomputable def gysinCycle
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (delta : S → ℤ) [IsDimensionFunction delta] (D : X.IdealSheafData)
    [IsLocallyPrincipalClosedSubscheme D.subschemeι]
    (N : D.subscheme.Modules) [Scheme.Modules.Invertible N]
    (sigma : Scheme.Modules.dual N ⟶
      (Scheme.Modules.pullback D.subschemeι).obj
        (RingedSpace.Hom.kernelIdealSheaf D.subschemeι.toShHom))
    [Epi sigma] (k : ℤ) (alpha : CycleGroup X (p.relativeDimensionFunction delta) (k + 1)) :
    CycleGroup D.subscheme ((D.subschemeι ≫ p).relativeDimensionFunction delta) k :=
  CycleGroup.locallyFiniteSum ((D.subschemeι ≫ p).relativeDimensionFunction delta) k
    (fun x : X ↦
      if hx : p.relativeDimensionFunction delta x = k + 1 then
        (CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction delta) (k + 1) alpha x) •
          gysinGeneratorCycle p delta D N sigma k x hx
      else 0)
    (gysinGeneratorTermsLocallyFinite p delta D N sigma k alpha)

/-- The generalized Gysin cycle sends zero to zero. -/
theorem gysinCycle_zero
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (delta : S → ℤ) [IsDimensionFunction delta] (D : X.IdealSheafData)
    [IsLocallyPrincipalClosedSubscheme D.subschemeι]
    (N : D.subscheme.Modules) [Scheme.Modules.Invertible N]
    (sigma : Scheme.Modules.dual N ⟶
      (Scheme.Modules.pullback D.subschemeι).obj
        (RingedSpace.Hom.kernelIdealSheaf D.subschemeι.toShHom))
    [Epi sigma] (k : ℤ) : gysinCycle p delta D N sigma k 0 = 0 := sorry

/-- The generalized Gysin cycle preserves addition. -/
theorem gysinCycle_add
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (delta : S → ℤ) [IsDimensionFunction delta] (D : X.IdealSheafData)
    [IsLocallyPrincipalClosedSubscheme D.subschemeι]
    (N : D.subscheme.Modules) [Scheme.Modules.Invertible N]
    (sigma : Scheme.Modules.dual N ⟶
      (Scheme.Modules.pullback D.subschemeι).obj
        (RingedSpace.Hom.kernelIdealSheaf D.subschemeι.toShHom))
    [Epi sigma] (k : ℤ)
    (alpha beta : CycleGroup X (p.relativeDimensionFunction delta) (k + 1)) :
    gysinCycle p delta D N sigma k (alpha + beta) =
      gysinCycle p delta D N sigma k alpha + gysinCycle p delta D N sigma k beta := sorry

/-- Taking the Chow class of the generalized Gysin cycle sends zero to zero. -/
theorem gysinCycleClass_zero
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (delta : S → ℤ) [IsDimensionFunction delta] (D : X.IdealSheafData)
    [IsLocallyPrincipalClosedSubscheme D.subschemeι]
    (N : D.subscheme.Modules) [Scheme.Modules.Invertible N]
    (sigma : Scheme.Modules.dual N ⟶
      (Scheme.Modules.pullback D.subschemeι).obj
        (RingedSpace.Hom.kernelIdealSheaf D.subschemeι.toShHom))
    [Epi sigma] (k : ℤ) :
    @chowClass D.subscheme
        (@subschemeIsLocallyNoetherian X (LocallyOfFiniteType.isLocallyNoetherian p) D)
        ((D.subschemeι ≫ p).relativeDimensionFunction delta) inferInstance k
        (gysinCycle p delta D N sigma k 0) = 0 := sorry

/-- Taking the Chow class of the generalized Gysin cycle preserves addition. -/
theorem gysinCycleClass_add
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (delta : S → ℤ) [IsDimensionFunction delta] (D : X.IdealSheafData)
    [IsLocallyPrincipalClosedSubscheme D.subschemeι]
    (N : D.subscheme.Modules) [Scheme.Modules.Invertible N]
    (sigma : Scheme.Modules.dual N ⟶
      (Scheme.Modules.pullback D.subschemeι).obj
        (RingedSpace.Hom.kernelIdealSheaf D.subschemeι.toShHom))
    [Epi sigma] (k : ℤ)
    (alpha beta : CycleGroup X (p.relativeDimensionFunction delta) (k + 1)) :
    @chowClass D.subscheme
        (@subschemeIsLocallyNoetherian X (LocallyOfFiniteType.isLocallyNoetherian p) D)
        ((D.subschemeι ≫ p).relativeDimensionFunction delta) inferInstance k
        (gysinCycle p delta D N sigma k (alpha + beta)) =
      @chowClass D.subscheme
          (@subschemeIsLocallyNoetherian X (LocallyOfFiniteType.isLocallyNoetherian p) D)
          ((D.subschemeι ≫ p).relativeDimensionFunction delta) inferInstance k
          (gysinCycle p delta D N sigma k alpha) +
        @chowClass D.subscheme
          (@subschemeIsLocallyNoetherian X (LocallyOfFiniteType.isLocallyNoetherian p) D)
          ((D.subschemeι ≫ p).relativeDimensionFunction delta) inferInstance k
          (gysinCycle p delta D N sigma k beta) := sorry

/-- An invertible module `N` on a locally principal closed subscheme `D` and an
epimorphism from the dual of `N` to the pulled-back ideal sheaf determine a generalized
degree-lowering Gysin homomorphism from cycles on the ambient scheme to Chow classes on `D`. -/
noncomputable def gysin
    {S X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    (p : X ⟶ S) [LocallyOfFiniteType p] (D : X.IdealSheafData)
    [IsLocallyPrincipalClosedSubscheme D.subschemeι]
    (N : D.subscheme.Modules) [Scheme.Modules.Invertible N]
    (sigma : Scheme.Modules.dual N ⟶
      (Scheme.Modules.pullback D.subschemeι).obj
        (RingedSpace.Hom.kernelIdealSheaf D.subschemeι.toShHom))
    [Epi sigma] (k : ℤ) :
    CycleGroup X (p.relativeDimensionFunction delta) (k + 1) →+
      @ChowGroup D.subscheme
        (@Scheme.IdealSheafData.subschemeIsLocallyNoetherian X
          (LocallyOfFiniteType.isLocallyNoetherian p) D)
        ((D.subschemeι ≫ p).relativeDimensionFunction delta) inferInstance k where
  toFun := fun alpha ↦ @chowClass D.subscheme
    (@Scheme.IdealSheafData.subschemeIsLocallyNoetherian X
      (LocallyOfFiniteType.isLocallyNoetherian p) D)
    ((D.subschemeι ≫ p).relativeDimensionFunction delta) inferInstance k
    (D.gysinCycle p delta N sigma k alpha)
  map_zero' := D.gysinCycleClass_zero p delta N sigma k
  map_add' := D.gysinCycleClass_add p delta N sigma k

/-- The generalized Gysin map is induced by the explicit pointwise cycle construction. -/
theorem gysin_apply
    {S X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    (p : X ⟶ S) [LocallyOfFiniteType p] (D : X.IdealSheafData)
    [IsLocallyPrincipalClosedSubscheme D.subschemeι]
    (N : D.subscheme.Modules) [Scheme.Modules.Invertible N]
    (sigma : Scheme.Modules.dual N ⟶
      (Scheme.Modules.pullback D.subschemeι).obj
        (RingedSpace.Hom.kernelIdealSheaf D.subschemeι.toShHom))
    [Epi sigma] (k : ℤ) (alpha : CycleGroup X (p.relativeDimensionFunction delta) (k + 1)) :
    gysin delta p D N sigma k alpha =
      @chowClass D.subscheme
        (@Scheme.IdealSheafData.subschemeIsLocallyNoetherian X
          (LocallyOfFiniteType.isLocallyNoetherian p) D)
        ((D.subschemeι ≫ p).relativeDimensionFunction delta) inferInstance k
        (D.gysinCycle p delta N sigma k alpha) := sorry

/-- For a regular section, the generalized ideal-surjection construction recovers the
zero-section Gysin homomorphism when `N` is the restricted ambient line bundle. -/
theorem gysin_zeroIdealSheaf
    {S X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    (p : X ⟶ S) [LocallyOfFiniteType p]
    (L : X.Modules) [Scheme.Modules.Invertible L] (s : L.sections)
    [RingedSpace.IsRegularSection L s]
    (sigma : Scheme.Modules.dual
        ((Scheme.Modules.pullback (Scheme.zeroIdealSheaf L s).subschemeι).obj L) ⟶
      (Scheme.Modules.pullback (Scheme.zeroIdealSheaf L s).subschemeι).obj
        (RingedSpace.Hom.kernelIdealSheaf
          (Scheme.zeroIdealSheaf L s).subschemeι.toShHom))
    [Epi sigma] (k : ℤ) :
    gysin delta p (Scheme.zeroIdealSheaf L s)
        ((Scheme.Modules.pullback (Scheme.zeroIdealSheaf L s).subschemeι).obj L) sigma k =
      Scheme.Modules.gysin p delta L s k := sorry

end AlgebraicGeometry.Scheme.IdealSheafData
