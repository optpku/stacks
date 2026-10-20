/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Curve

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.RingedSpace.ModuleDerived
open DerivedCategory.ShiftedHom.Boundary
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace DerivedQCoh
namespace ProperDualizingComplex

/- The degree-`-1` cohomology sheaf of the proper dualizing complex of a scheme over a
field. -/
#check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.curveDualizingModule :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f],
    X.Modules)

/- The curve dualizing module is the degree-`-1` cohomology sheaf of the proper
dualizing complex. -/
#check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.curveDualizingModule_eq :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f],
    curveDualizingModule f =
      RingedSpace.ModuleDerived.cohomologySheaf (properDualizingComplex f).obj (-1))

/- The canonical boundary map from degree-`-1` derived `Ext` to morphisms into the
curve dualizing module. -/
#check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.curveModuleBoundary :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] (F : QCoh X),
    Ext⁽(-1 : ℤ)⁾(moduleObject F, properDualizingComplex f) →
      (((QCoh.toRingedSpace X).obj F).obj ⟶ curveDualizingModule f))

/- Evaluation of `curveModuleBoundary` is the canonical cohomological boundary map
after forgetting to ambient derived modules. -/
#check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.curveModuleBoundary_app :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] (F : QCoh X)
    (g : Ext⁽(-1 : ℤ)⁾(moduleObject F, properDualizingComplex f)),
    curveModuleBoundary f F g =
      let degreeEq : (-1 : ℤ) = -1 - 0 := (Int.sub_zero _).symm
      let g' : ShiftedHom (moduleObject F).obj (properDualizingComplex f).obj
          ((-1 : ℤ) - 0) :=
        ShiftedHom.map g (DerivedQCoh.inclusion X) ≫
          eqToHom (congrArg
            (fun n : ℤ ↦ (properDualizingComplex f).obj⟦n⟧) degreeEq)
      (DerivedCategory.singleFunctorCompHomologyFunctorIso
          X.toRingedSpace.Modules 0).inv.app ((QCoh.toRingedSpace X).obj F).obj ≫
        toHomology (moduleObject F).obj (properDualizingComplex f).obj 0 (-1) g')

/- In dimension at most one, the boundary map from degree-`-1` derived `Ext` to
morphisms into the curve dualizing module is bijective. -/
#check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.curveModuleBoundary_bijective :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left ≤ 1) (F : QCoh X.left),
    Function.Bijective (curveModuleBoundary X.hom F))

/- The direct comparison from morphisms into the curve dualizing module to the
ground-field dual of first proper cohomology. -/
#check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.curveModuleDualityComparison :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] (F : QCoh X),
    (((QCoh.toRingedSpace X).obj F).obj ⟶ curveDualizingModule f) →
      (cohomologyOverField f (moduleObject F) 1 ⟶ fieldObject k))

/- In dimension at most one, the curve-module comparison on an element produced by
`curveModuleBoundary` is the derived `Ext` comparison in degree `-1`. -/
#check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.curveModuleDualityComparison_curveModuleBoundary :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left ≤ 1) (F : QCoh X.left)
    (g : Ext⁽(-1 : ℤ)⁾(moduleObject F, properDualizingComplex X.hom)),
    curveModuleDualityComparison X.hom F (curveModuleBoundary X.hom F g) =
      eqToHom (congrArg (cohomologyOverField X.hom (moduleObject F))
        (Int.neg_neg (1 : ℤ)).symm) ≫
        extComparison X.hom (-1) (moduleObject F) g)
end ProperDualizingComplex
end DerivedQCoh
end Scheme
end AlgebraicGeometry
