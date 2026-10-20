/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Duality
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Locality
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Depth
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Support
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.DifferentialExterior
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.ExteriorPower

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.RingedSpace.ModuleDerived
open scoped ENat DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace DerivedQCoh
namespace ProperDualizingComplex

/-- the chosen right-adjoint image of the ground-field structure sheaf is
a dualizing complex on the proper scheme. -/
theorem isDualizing
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] :
    @Scheme.IsDualizingComplex X (LocallyOfFiniteType.isLocallyNoetherian f)
      (properDualizingComplex f).obj := sorry

/-- nonzero cohomology of the proper dualizing complex occurs only in
degrees from `-dimensionIndex f` through `0`. -/
theorem nonzero_degreeBounds
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] (i : ℤ)
    (hi : ¬ IsZero (RingedSpace.ModuleDerived.cohomologySheaf
      (properDualizingComplex f).obj i)) :
    -(dimensionIndex f : ℤ) ≤ i ∧ i ≤ 0 := sorry

/-- the bottom cohomology module of the proper dualizing complex is
coherent. -/
instance dualizingModule_isCoherent
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] :
    (dualizingModule f).IsCoherent := sorry

/-- the dualizing module satisfies Serre's condition `(S₂)`. -/
theorem dualizingModule_satisfiesSerreConditionSTwo
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] :
    @Scheme.Modules.satisfiesSerreConditionS X
      (LocallyOfFiniteType.isLocallyNoetherian f) (dualizingModule f)
      (dualizingModule_isCoherent f) 2 := sorry

/-- the support of the dualizing module is the union of the
irreducible components having the same dimension as the scheme. -/
theorem dualizingModule_support
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] :
    RingedSpace.moduleSupport (dualizingModule f) =
      ⋃ Z : irreducibleComponents X,
        ⋃ (_ : topologicalKrullDim Z = topologicalKrullDim X), (Z : Set X) := sorry

/-- in every nonpositive degree, the support of cohomology has
dimension at most the opposite degree. -/
theorem supportDimension_le
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (i : ℤ) (hi : i ≤ 0) :
    topologicalKrullDim
        (RingedSpace.moduleSupport (RingedSpace.ModuleDerived.cohomologySheaf
          (properDualizingComplex f).obj i)) ≤
      ((-i).toNat : WithBot ℕ∞) := sorry

/-- at a closed point, some stalk cohomology between degrees `i` and
`0` is nontrivial exactly when the local ring has depth at most `-i`. -/
theorem stalk_nontrivialUpTo_iff_depth
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (x : X) (hx : x ∈ closedPoints X) (i : ℤ) (hi : i ≤ 0) :
    (∃ j : ℤ, i ≤ j ∧ j ≤ 0 ∧
      Nontrivial (cohomologyStalk (properDualizingComplex f).obj j x)) ↔
      moduleDepth (X.presheaf.stalk x) (X.presheaf.stalk x) ≤
        ((-i).toNat : ℕ∞) := sorry

/-- the canonical comparison from derived `Ext` to the dual of
proper cohomology over the ground field is bijective. -/
theorem extComparison_bijective
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (i : ℤ) (K : DerivedQCoh X) :
    Function.Bijective (extComparison f i K) := sorry

/-- the proper-duality comparison commutes with the canonical
reindexing isomorphisms for a shifted object. -/
theorem extComparison_shift
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (i n : ℤ) (K : DerivedQCoh X)
    (g : Ext⁽i⁾(K⟦n⟧, properDualizingComplex f)) :
    (cohomologyShiftIso f i n K).hom ≫
        extComparison f (i - n) K (extSourceShift f i n K g) =
      extComparison f i (K⟦n⟧) g := sorry

/-- for a distinguished triangle, the proper-duality comparison
commutes with its connecting morphism. -/
theorem extComparison_distinguishedBoundary
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (T : Pretriangulated.Triangle (DerivedQCoh X))
    (hT : T ∈ distTriang (DerivedQCoh X)) (i : ℤ)
    (g : Ext⁽i⁾(T.obj₁⟦(1 : ℤ)⟧, properDualizingComplex f)) :
    extComparison f i T.obj₃ (T.mor₃ ≫ g) =
      cohomologyOverFieldMap f T.mor₃ (-i) ≫
        extComparison f i (T.obj₁⟦(1 : ℤ)⟧) g := sorry

/-- for every quasicoherent module, the canonical comparison from
morphisms into the dualizing module to the ground-field dual of top-degree proper cohomology
is bijective. -/
theorem moduleDualityComparison_bijective
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] (F : QCoh X) :
    Function.Bijective (moduleDualityComparison f F) := sorry

/-- for a smooth proper scheme of relative dimension `d`, the
proper dualizing complex is isomorphic to the shifted top exterior power of differentials. -/
theorem smooth_isomorphic_differentialExteriorShift
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (d : ℕ) [SmoothOfRelativeDimension d f] :
    IsIsomorphic (properDualizingComplex f)
      (Scheme.Hom.differentialExteriorShift f d) := sorry

/-- in the smooth case, the dualizing module is isomorphic to the
top exterior power of relative differentials. -/
theorem smooth_dualizingModule_isomorphic_exteriorPower
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (d : ℕ) [SmoothOfRelativeDimension d f] :
    IsIsomorphic (dualizingModule f)
      (RingedSpace.ExteriorPower.sheaf (Ω[f.toShHom]) d) := sorry

end ProperDualizingComplex
end DerivedQCoh
end Scheme
end AlgebraicGeometry
