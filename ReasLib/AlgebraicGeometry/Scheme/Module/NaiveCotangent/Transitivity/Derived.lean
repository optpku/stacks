/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent.Transitivity
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyOfType
public import ReasLib.RingTheory.CompleteIntersection.Local.RingHom
public import ReasLib.RingTheory.Extension.Cotangent.JacobiZariski
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Pretriangulated DerivedCategory
open AlgebraicGeometry.RingedSpace.NaiveCotangent

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.NaiveCotangent

/-- A local complete-intersection hypothesis makes the canonical transitivity map to the
mapping cocone a quasi-isomorphism. -/
theorem toCocone_quasiIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f] :
    QuasiIso (RingedSpace.NaiveCotangent.transitivity f.toShHom g.toShHom).toCocone := sorry

/-- The derived image of the transitivity map to the mapping cocone is invertible. -/
instance toCoconeQ_isIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f] :
    IsIso (DerivedCategory.Q.map
      (RingedSpace.NaiveCotangent.transitivity f.toShHom g.toShHom).toCocone) := sorry

/-- The canonical derived comparison from the chosen representative of `f^* NL(Y/Z)` to the
mapping cocone of `NL(X/Z) ⟶ NL(X/Y)`. -/
noncomputable def derivedCoconeIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f] :
    ((DerivedCategory.Q : (CochainComplex X.toRingedSpace.Modules ℤ) ⥤
        RingedSpace.ModuleDerived X.toRingedSpace).obj
      (Pullback.chosenComplex f.toShHom g.toShHom)) ≅
      ((DerivedCategory.Q : (CochainComplex X.toRingedSpace.Modules ℤ) ⥤
          RingedSpace.ModuleDerived X.toRingedSpace).obj
        (CochainComplex.mappingCocone
          (RingedSpace.NaiveCotangent.transitivity f.toShHom g.toShHom).comparison)) :=
  DerivedCategory.Q.mapIso
      (Pullback.chosenComplexIso f.toShHom g.toShHom) ≪≫
    asIso (DerivedCategory.Q.map
      (RingedSpace.NaiveCotangent.transitivity f.toShHom g.toShHom).toCocone)

/-- The forward map of `derivedCoconeIso` is the chosen-pullback comparison followed by the
derived transitivity map. -/
theorem derivedCoconeIso_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f] :
    (derivedCoconeIso f g).hom =
      DerivedCategory.Q.map
          (Pullback.chosenComplexIso f.toShHom g.toShHom).hom ≫
        DerivedCategory.Q.map
          (RingedSpace.NaiveCotangent.transitivity f.toShHom g.toShHom).toCocone := sorry

/-- The canonical naive-cotangent transitivity triangle
`f^* NL(Y/Z) ⟶ NL(X/Z) ⟶ NL(X/Y) ⟶ f^* NL(Y/Z)⟦1⟧` in `D(𝒪_X)`. -/
@[stacks 0FV3]
noncomputable def triangle {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f] :
    Triangle (RingedSpace.ModuleDerived X.toRingedSpace) :=
  let t := RingedSpace.NaiveCotangent.transitivity f.toShHom g.toShHom
  let e := derivedCoconeIso f g
  let T : Triangle (RingedSpace.ModuleDerived X.toRingedSpace) :=
    Q.mapTriangle.obj (CochainComplex.mappingCocone.triangle t.comparison)
  Triangle.mk (e.hom ≫ T.mor₁) T.mor₂ (T.mor₃ ≫ e.inv⟦1⟧')

/-- The first map of `triangle` is the chosen-pullback comparison followed by the mapping-cocone
projection. -/
theorem triangle_mor₁ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f] :
    (triangle f g).mor₁ = (derivedCoconeIso f g).hom ≫
      (Q.mapTriangle.obj (CochainComplex.mappingCocone.triangle
        (RingedSpace.NaiveCotangent.transitivity f.toShHom g.toShHom).comparison)).mor₁ := sorry

/-- The middle map of `triangle` is the derived image of the naive-cotangent comparison. -/
theorem triangle_mor₂ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f] :
    (triangle f g).mor₂ = DerivedCategory.Q.map
      (RingedSpace.NaiveCotangent.transitivity f.toShHom g.toShHom).comparison := sorry

/-- The boundary map of `triangle` is the mapping-cocone boundary transported back to the
chosen pullback representative. -/
theorem triangle_mor₃ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f] :
    (triangle f g).mor₃ =
      (Q.mapTriangle.obj (CochainComplex.mappingCocone.triangle
        (RingedSpace.NaiveCotangent.transitivity f.toShHom g.toShHom).comparison)).mor₃ ≫
        (derivedCoconeIso f g).inv⟦1⟧' := sorry

/-- Compatibility of the first map with the mapping-cocone triangle. -/
theorem triangleIso_comm_left {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f] :
    let t := RingedSpace.NaiveCotangent.transitivity f.toShHom g.toShHom
    let T := Q.mapTriangle.obj (CochainComplex.mappingCocone.triangle t.comparison)
    (triangle f g).mor₁ ≫ (Iso.refl T.obj₂).hom = (derivedCoconeIso f g).hom ≫ T.mor₁ := sorry

/-- Compatibility of the middle map with the mapping-cocone triangle. -/
theorem triangleIso_comm_comparison {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f] :
    let t := RingedSpace.NaiveCotangent.transitivity f.toShHom g.toShHom
    let T := Q.mapTriangle.obj (CochainComplex.mappingCocone.triangle t.comparison)
    (triangle f g).mor₂ ≫ (Iso.refl T.obj₃).hom = (Iso.refl T.obj₂).hom ≫ T.mor₂ := sorry

/-- Compatibility of the boundary map with the mapping-cocone triangle. -/
theorem triangleIso_comm_boundary {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f] :
    let t := RingedSpace.NaiveCotangent.transitivity f.toShHom g.toShHom
    let T := Q.mapTriangle.obj (CochainComplex.mappingCocone.triangle t.comparison)
    (triangle f g).mor₃ ≫ (derivedCoconeIso f g).hom⟦1⟧' =
      (Iso.refl T.obj₃).hom ≫ T.mor₃ := sorry

/-- The canonical naive-cotangent triangle is isomorphic to the mapped mapping-cocone
triangle. -/
noncomputable def triangleIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f] :
    triangle f g ≅ Q.mapTriangle.obj (CochainComplex.mappingCocone.triangle
      (RingedSpace.NaiveCotangent.transitivity f.toShHom g.toShHom).comparison) :=
  Triangle.isoMk _ _ (derivedCoconeIso f g) (Iso.refl _) (Iso.refl _)
    (triangleIso_comm_left f g) (triangleIso_comm_comparison f g)
    (triangleIso_comm_boundary f g)

/-- The first component of `triangleIso` is `derivedCoconeIso`. -/
theorem triangleIso_hom_hom₁ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f] :
    (triangleIso f g).hom.hom₁ = (derivedCoconeIso f g).hom := sorry

/-- The canonical naive-cotangent triangle is distinguished. -/
@[stacks 0FV3]
theorem triangle_distinguished {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f] :
    triangle f g ∈ distTriang (RingedSpace.ModuleDerived X.toRingedSpace) := sorry

/-- Compatibility of the degree `-1` left map in the derived and cochain six-term sequences. -/
theorem sixTermIso_comm_left_negOne {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f] :
    let t := RingedSpace.NaiveCotangent.transitivity f.toShHom g.toShHom
    let A := CategoryTheory.Functor.homologySequenceComposableArrows₅
      (DerivedCategory.homologyFunctor X.toRingedSpace.Modules 0) (triangle f g) (-1) 0 rfl
    A.map' 0 1 ≫
        (DerivedCategory.homologyFunctorFactors X.toRingedSpace.Modules (-1)).hom.app
          (RingedSpace.naiveCotangent (f.toShHom ≫ g.toShHom)) =
      (((DerivedCategory.homologyFunctorFactors X.toRingedSpace.Modules (-1)).app
          (Pullback.chosenComplex f.toShHom g.toShHom)) ≪≫
        (HomologicalComplex.homologyFunctor X.toRingedSpace.Modules
          (ComplexShape.up ℤ) (-1)).mapIso
            (Pullback.chosenComplexIso
              f.toShHom g.toShHom)).hom ≫
        t.sixTerm.map' 0 1 := sorry

/-- Compatibility of the degree `-1` comparison map in the two six-term sequences. -/
theorem sixTermIso_comm_comparison_negOne {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyOfType RingHom.IsLocalCompleteIntersection f] :
    let t := RingedSpace.NaiveCotangent.transitivity f.toShHom g.toShHom
    let A := CategoryTheory.Functor.homologySequenceComposableArrows₅
      (DerivedCategory.homologyFunctor X.toRingedSpace.Modules 0) (triangle f g) (-1) 0 rfl
    A.map' 1 2 ≫
        (DerivedCategory.homologyFunctorFactors X.toRingedSpace.Modules (-1)).hom.app
          (RingedSpace.naiveCotangent f.toShHom) =
      (DerivedCategory.homologyFunctorFactors X.toRingedSpace.Modules (-1)).hom.app
          (RingedSpace.naiveCotangent (f.toShHom ≫ g.toShHom)) ≫
        t.sixTerm.map' 1 2 := sorry

/-- Compatibility of the boundary map in the two six-term sequences. -/
theorem sixTermIso_comm_boundary {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f] :
    let t := RingedSpace.NaiveCotangent.transitivity f.toShHom g.toShHom
    let A := CategoryTheory.Functor.homologySequenceComposableArrows₅
      (DerivedCategory.homologyFunctor X.toRingedSpace.Modules 0) (triangle f g) (-1) 0 rfl
    A.map' 2 3 ≫
        (((DerivedCategory.homologyFunctorFactors X.toRingedSpace.Modules 0).app
            (Pullback.chosenComplex f.toShHom g.toShHom)) ≪≫
          (HomologicalComplex.homologyFunctor X.toRingedSpace.Modules
            (ComplexShape.up ℤ) 0).mapIso
              (Pullback.chosenComplexIso
                f.toShHom g.toShHom)).hom =
      (DerivedCategory.homologyFunctorFactors X.toRingedSpace.Modules (-1)).hom.app
          (RingedSpace.naiveCotangent f.toShHom) ≫
        t.sixTerm.map' 2 3 := sorry

/-- Compatibility of the degree `0` left map in the derived and cochain six-term sequences. -/
theorem sixTermIso_comm_left_zero {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f] :
    let t := RingedSpace.NaiveCotangent.transitivity f.toShHom g.toShHom
    let A := CategoryTheory.Functor.homologySequenceComposableArrows₅
      (DerivedCategory.homologyFunctor X.toRingedSpace.Modules 0) (triangle f g) (-1) 0 rfl
    A.map' 3 4 ≫
        (DerivedCategory.homologyFunctorFactors X.toRingedSpace.Modules 0).hom.app
          (RingedSpace.naiveCotangent (f.toShHom ≫ g.toShHom)) =
      (((DerivedCategory.homologyFunctorFactors X.toRingedSpace.Modules 0).app
          (Pullback.chosenComplex f.toShHom g.toShHom)) ≪≫
        (HomologicalComplex.homologyFunctor X.toRingedSpace.Modules
          (ComplexShape.up ℤ) 0).mapIso
            (Pullback.chosenComplexIso
              f.toShHom g.toShHom)).hom ≫
        t.sixTerm.map' 3 4 := sorry

/-- Compatibility of the degree `0` comparison map in the two six-term sequences. -/
theorem sixTermIso_comm_comparison_zero {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyOfType RingHom.IsLocalCompleteIntersection f] :
    let t := RingedSpace.NaiveCotangent.transitivity f.toShHom g.toShHom
    let A := CategoryTheory.Functor.homologySequenceComposableArrows₅
      (DerivedCategory.homologyFunctor X.toRingedSpace.Modules 0) (triangle f g) (-1) 0 rfl
    A.map' 4 5 ≫
        (DerivedCategory.homologyFunctorFactors X.toRingedSpace.Modules 0).hom.app
          (RingedSpace.naiveCotangent f.toShHom) =
      (DerivedCategory.homologyFunctorFactors X.toRingedSpace.Modules 0).hom.app
          (RingedSpace.naiveCotangent (f.toShHom ≫ g.toShHom)) ≫
        t.sixTerm.map' 4 5 := sorry

/-- The canonical six-term homology segment of `triangle f g` is canonically isomorphic to
the naive-cotangent transitivity sequence. -/
@[stacks 0FV3]
noncomputable def sixTermIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f] :
    CategoryTheory.Functor.homologySequenceComposableArrows₅
        (DerivedCategory.homologyFunctor X.toRingedSpace.Modules 0)
        (triangle f g) (-1) 0 rfl ≅
      (RingedSpace.NaiveCotangent.transitivity f.toShHom g.toShHom).sixTerm :=
  ComposableArrows.isoMk₅
    (((DerivedCategory.homologyFunctorFactors X.toRingedSpace.Modules (-1)).app
        (Pullback.chosenComplex f.toShHom g.toShHom)) ≪≫
      (HomologicalComplex.homologyFunctor X.toRingedSpace.Modules
        (ComplexShape.up ℤ) (-1)).mapIso
          (Pullback.chosenComplexIso f.toShHom g.toShHom))
    ((DerivedCategory.homologyFunctorFactors X.toRingedSpace.Modules (-1)).app
      (RingedSpace.naiveCotangent (f.toShHom ≫ g.toShHom)))
    ((DerivedCategory.homologyFunctorFactors X.toRingedSpace.Modules (-1)).app
      (RingedSpace.naiveCotangent f.toShHom))
    (((DerivedCategory.homologyFunctorFactors X.toRingedSpace.Modules 0).app
        (Pullback.chosenComplex f.toShHom g.toShHom)) ≪≫
      (HomologicalComplex.homologyFunctor X.toRingedSpace.Modules
        (ComplexShape.up ℤ) 0).mapIso
          (Pullback.chosenComplexIso f.toShHom g.toShHom))
    ((DerivedCategory.homologyFunctorFactors X.toRingedSpace.Modules 0).app
      (RingedSpace.naiveCotangent (f.toShHom ≫ g.toShHom)))
    ((DerivedCategory.homologyFunctorFactors X.toRingedSpace.Modules 0).app
      (RingedSpace.naiveCotangent f.toShHom))
    (sixTermIso_comm_left_negOne f g) (sixTermIso_comm_comparison_negOne f g)
    (sixTermIso_comm_boundary f g) (sixTermIso_comm_left_zero f g)
    (sixTermIso_comm_comparison_zero f g)

/-- The first component of `sixTermIso` is the canonical comparison from derived homology to
the homology of the chosen pullback complex. -/
theorem sixTermIso_hom_app_zero {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f] :
    (sixTermIso f g).hom.app 0 =
      (((DerivedCategory.homologyFunctorFactors X.toRingedSpace.Modules (-1)).app
          (Pullback.chosenComplex f.toShHom g.toShHom)) ≪≫
        (HomologicalComplex.homologyFunctor X.toRingedSpace.Modules
          (ComplexShape.up ℤ) (-1)).mapIso
            (Pullback.chosenComplexIso
              f.toShHom g.toShHom)).hom := sorry

end AlgebraicGeometry.Scheme.Hom.NaiveCotangent
