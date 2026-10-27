/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.InverseImage
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NaiveCotangent.Ext
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NaiveCotangent.InverseImage
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.Composition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Adjunction.Opens
public import ReasLib.CategoryTheory.Shift.ShiftedHom.Adjunction
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Exact

/-! # Derived Ext comparison for inverse-image ringed spaces -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.RingedSpace AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Thickening
open SheafOfModules.RingedSite
open TopologicalSpace Opposite
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.NaiveCotangent.InverseImage

variable {S X Y : RingedSpace.{u}}

/-- Derived pullback along `g` is the composite `L(inverseImageTo g)^* ⋙ L(fromInverseImage g)^*`,
via `modulePullbackDerived.compIso` and `fromInverseImage_comp`. -/
def derivedPullbackCompIso_fromInverseImage (g : Y ⟶ X) :
    modulePullbackDerived (inverseImageTo g) ⋙
        modulePullbackDerived (fromInverseImage g) ≅
      modulePullbackDerived g :=
  (modulePullbackDerived.compIso (fromInverseImage g) (inverseImageTo g)
      (modulePullbackDerived.compComparison_isIso (fromInverseImage g)
        (inverseImageTo g))) ≪≫
    eqToIso
      (congrArg (fun h : Y ⟶ X ↦ modulePullbackDerived h) (fromInverseImage_comp g))

/-- The forward map of `derivedPullbackCompIso_fromInverseImage` is the composition comparison
followed by transport along `fromInverseImage_comp`. -/
theorem derivedPullbackCompIso_fromInverseImage_hom (g : Y ⟶ X) :
    (derivedPullbackCompIso_fromInverseImage g).hom =
      (modulePullbackDerived.compIso (fromInverseImage g) (inverseImageTo g)
          (modulePullbackDerived.compComparison_isIso (fromInverseImage g)
            (inverseImageTo g))).hom ≫
        (eqToIso
          (congrArg (fun h : Y ⟶ X ↦ modulePullbackDerived h)
            (fromInverseImage_comp g))).hom := rfl

/-- Forward map of the displayed Ext¹ identification: pull back along
`fromInverseImage`, compare naive cotangents, then transport along
`derivedPullbackCompIso_fromInverseImage` into `Ext¹(L(g)^* NL[f], G)`. -/
def extOne_inverseImage (f : X ⟶ S) (g : Y ⟶ X) (G : Y.Modules)
    (ξ :
      Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := (inverseImageSpace g).Modules)).obj NL[inverseImageTo g ≫ f],
        (DerivedCategory.Q (C := (inverseImageSpace g).Modules)).obj
          ((CochainComplex.singleFunctor (inverseImageSpace g).Modules 0).obj
            (restrictToInverseImage g G)))) :
    Ext⁽(1 : ℤ)⁾((modulePullbackDerived g).obj ((DerivedCategory.Q (C := X.Modules)).obj NL[f]),
      (DerivedCategory.Q (C := Y.Modules)).obj ((CochainComplex.singleFunctor Y.Modules 0).obj G)) :=
  ShiftedHom.comp
    (ShiftedHom.mk₀ (0 : ℤ) rfl
      ((derivedPullbackCompIso_fromInverseImage g).inv.app ((DerivedCategory.Q (C := X.Modules)).obj NL[f])))
    (ShiftedHom.comp
      (ShiftedHom.mk₀ (0 : ℤ) rfl
        ((modulePullbackDerived (fromInverseImage g)).map
          (naiveCotangentComparison f (inverseImageTo g))))
      (ShiftedHom.comp
        ((modulePullbackDerived (fromInverseImage g)).map ξ ≫
          ((modulePullbackDerived.commShift (fromInverseImage g)).commShiftIso
              (1 : ℤ)).hom.app
            ((DerivedCategory.Q (C := (inverseImageSpace g).Modules)).obj
              ((CochainComplex.singleFunctor (inverseImageSpace g).Modules 0).obj
                (restrictToInverseImage g G))))
        (ShiftedHom.mk₀ (0 : ℤ) rfl (coeffDerived ((pullbackPushforwardAdjunction (fromInverseImage g)).counit.app G)))
        (zero_add (1 : ℤ)))
      (add_zero (1 : ℤ)))
    (add_zero (1 : ℤ))

/-- Inverse image of the structure sheaves induces an isomorphism on derived naive cotangents. -/
instance naiveCotangentComparison_isIso (f : X ⟶ S) (g : Y ⟶ X) :
    IsIso (naiveCotangentComparison f (inverseImageTo g)) := sorry

/-- Inverse image and derived tensor–Hom adjunction identify
Ext¹_{g⁻¹ 𝒪_X}(NL_{g⁻¹ 𝒪_X / g⁻¹ f⁻¹ 𝒪_S}, G) with
Ext¹_{𝒪_Y}(L(g)^* NL[f], G). -/
def extOne_inverseImageIso (f : X ⟶ S) (g : Y ⟶ X) (G : Y.Modules) :
    Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := (inverseImageSpace g).Modules)).obj NL[inverseImageTo g ≫ f],
      (DerivedCategory.Q (C := (inverseImageSpace g).Modules)).obj
        ((CochainComplex.singleFunctor (inverseImageSpace g).Modules 0).obj
          (restrictToInverseImage g G))) ≃
      Ext⁽(1 : ℤ)⁾((modulePullbackDerived g).obj ((DerivedCategory.Q (C := X.Modules)).obj NL[f]),
        (DerivedCategory.Q (C := Y.Modules)).obj ((CochainComplex.singleFunctor Y.Modules 0).obj G)) :=
  let A := (DerivedCategory.Q (C := X.Modules)).obj NL[f]
  let B := (DerivedCategory.Q (C := (inverseImageSpace g).Modules)).obj
    NL[inverseImageTo g ≫ f]
  let C := (DerivedCategory.Q (C := Y.Modules)).obj
    ((CochainComplex.singleFunctor Y.Modules 0).obj G)
  let coefficientIso :=
    ((((fromInverseImage g)_*).mapDerivedCategoryFactors.app
        ((CochainComplex.singleFunctor Y.Modules 0).obj G)) ≪≫
      (DerivedCategory.Q (C := (inverseImageSpace g).Modules)).mapIso
        ((HomologicalComplex.singleMapHomologicalComplex ((fromInverseImage g)_*)
          (ComplexShape.up ℤ) (0 : ℤ)).app G)).symm ≪≫
      (Functor.RightDerived.Exact.homotopyIso ((fromInverseImage g)_*)).app C
  let sourceIso :=
    (derivedPullbackCompIso_fromInverseImage g).symm.app A ≪≫
      (modulePullbackDerived (fromInverseImage g)).mapIso
        (asIso (naiveCotangentComparison f (inverseImageTo g)))
  (Iso.homCongr (Iso.refl B) ((shiftFunctor _ (1 : ℤ)).mapIso coefficientIso)).trans
    (((moduleDerivedAdjunctionOfOpens (fromInverseImage g)).shiftedHomEquiv
      B C (1 : ℤ)).trans
        (Iso.homCongr sourceIso.symm (Iso.refl (C⟦(1 : ℤ)⟧))))

/-- The inverse of the canonical derived tensor–Hom identification of Ext¹ groups. -/
def extOne_inverseImage_symm (f : X ⟶ S) (g : Y ⟶ X) (G : Y.Modules)
    (ζ : Ext⁽(1 : ℤ)⁾((modulePullbackDerived g).obj
        ((DerivedCategory.Q (C := X.Modules)).obj NL[f]),
      (DerivedCategory.Q (C := Y.Modules)).obj ((CochainComplex.singleFunctor Y.Modules 0).obj G))) :
    Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := (inverseImageSpace g).Modules)).obj NL[inverseImageTo g ≫ f],
      (DerivedCategory.Q (C := (inverseImageSpace g).Modules)).obj
        ((CochainComplex.singleFunctor (inverseImageSpace g).Modules 0).obj
          (restrictToInverseImage g G))) :=
  (extOne_inverseImageIso f g G).symm ζ

/-- The forward map of `extOne_inverseImageIso` is `extOne_inverseImage`. -/
theorem extOne_inverseImageIso_apply (f : X ⟶ S) (g : Y ⟶ X) (G : Y.Modules)
    (ξ :
      Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := (inverseImageSpace g).Modules)).obj NL[inverseImageTo g ≫ f],
        (DerivedCategory.Q (C := (inverseImageSpace g).Modules)).obj
          ((CochainComplex.singleFunctor (inverseImageSpace g).Modules 0).obj
            (restrictToInverseImage g G)))) :
    extOne_inverseImageIso f g G ξ = extOne_inverseImage f g G ξ := sorry

/-- The reverse map of `extOne_inverseImageIso` is `extOne_inverseImage_symm`. -/
theorem extOne_inverseImageIso_symm_apply (f : X ⟶ S) (g : Y ⟶ X) (G : Y.Modules)
    (ζ :
      Ext⁽(1 : ℤ)⁾((modulePullbackDerived g).obj ((DerivedCategory.Q (C := X.Modules)).obj NL[f]),
        (DerivedCategory.Q (C := Y.Modules)).obj ((CochainComplex.singleFunctor Y.Modules 0).obj G))) :
    (extOne_inverseImageIso f g G).symm ζ = extOne_inverseImage_symm f g G ζ := rfl

end AlgebraicGeometry.RingedSpace.NaiveCotangent.InverseImage
