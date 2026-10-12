/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.Dual
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.FiniteTypeOver
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Duality
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Uniqueness
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.NormalizedDualizing.Relative

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.TStructure
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.NewUpperShriek

/-- The ambient duality-pullback-duality functor associated to a morphism and chosen
dualizing complexes on its source and target. -/
noncomputable def ambient {X Y : Scheme.{u}} (f : X ⟶ Y)
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [BraidedCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    [MonoidalCategory (RingedSpace.ModuleDerived Y.toRingedSpace)]
    [BraidedCategory (RingedSpace.ModuleDerived Y.toRingedSpace)]
    (HY : MonoidalClosed (RingedSpace.ModuleDerived Y.toRingedSpace))
    (ωX : RingedSpace.ModuleDerived X.toRingedSpace)
    (ωY : RingedSpace.ModuleDerived Y.toRingedSpace) :
    CategoryTheory.Functor
      D⁺[SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf]
      (RingedSpace.ModuleDerived X.toRingedSpace) :=
  (((DerivedCategory.Plus.CohomologyIn.ambient
      (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf)).op ⋙
        (RightInternalHom.ofBraidedClosedOf HY).dualFunctor ωY) ⋙
      RingedSpace.modulePullbackDerived f.toLRSHom.toShHom).rightOp ⋙
    (RightInternalHom.ofBraidedClosedOf HX).dualFunctor ωX

/-- The value of the ambient new upper-shriek functor is the displayed
`Rℓom(Lf⁺Rℓom(K, ωY), ωX)` formula. -/
theorem ambient_obj {X Y : Scheme.{u}} (f : X ⟶ Y)
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [BraidedCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    [MonoidalCategory (RingedSpace.ModuleDerived Y.toRingedSpace)]
    [BraidedCategory (RingedSpace.ModuleDerived Y.toRingedSpace)]
    (HY : MonoidalClosed (RingedSpace.ModuleDerived Y.toRingedSpace))
    (ωX : RingedSpace.ModuleDerived X.toRingedSpace)
    (ωY : RingedSpace.ModuleDerived Y.toRingedSpace)
    (K : D⁺[SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf]) :
    (ambient f HX HY ωX ωY).obj K =
      (MonoidalClosed.ihomOf HX
        ((RingedSpace.modulePullbackDerived f.toLRSHom.toShHom).obj
          ((MonoidalClosed.ihomOf HY K.obj.obj).obj ωY))).obj ωX := sorry

/-- For a finite-type morphism and dualizing source and target complexes, the ambient
duality-pullback-duality functor takes values in the bounded-below derived category. -/
theorem boundedBelow {X Y : Scheme.{u}} (f : X ⟶ Y) [FiniteType f]
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [BraidedCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    [MonoidalCategory (RingedSpace.ModuleDerived Y.toRingedSpace)]
    [BraidedCategory (RingedSpace.ModuleDerived Y.toRingedSpace)]
    (HY : MonoidalClosed (RingedSpace.ModuleDerived Y.toRingedSpace))
    (ωX : RingedSpace.ModuleDerived X.toRingedSpace)
    (ωY : RingedSpace.ModuleDerived Y.toRingedSpace)
    (hωX : RingedSpace.ModuleDerived.IsDualizingComplex ωX HX)
    (hωY : RingedSpace.ModuleDerived.IsDualizingComplex ωY HY)
    (K : D⁺[SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf]) :
    (t.plus : ObjectProperty
      (RingedSpace.ModuleDerived X.toRingedSpace))
        ((ambient f HX HY ωX ωY).obj K) := sorry

/-- After lifting boundedness, the ambient duality-pullback-duality functor has coherent
cohomology. -/
theorem coherent {X Y : Scheme.{u}} (f : X ⟶ Y) [FiniteType f]
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [BraidedCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    [MonoidalCategory (RingedSpace.ModuleDerived Y.toRingedSpace)]
    [BraidedCategory (RingedSpace.ModuleDerived Y.toRingedSpace)]
    (HY : MonoidalClosed (RingedSpace.ModuleDerived Y.toRingedSpace))
    (ωX : RingedSpace.ModuleDerived X.toRingedSpace)
    (ωY : RingedSpace.ModuleDerived Y.toRingedSpace)
    (hωX : RingedSpace.ModuleDerived.IsDualizingComplex ωX HX)
    (hωY : RingedSpace.ModuleDerived.IsDualizingComplex ωY HY)
    (K : D⁺[SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf]) :
    DerivedCategory.Plus.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf)
      (((t.plus : ObjectProperty
        (RingedSpace.ModuleDerived X.toRingedSpace)).lift
          (ambient f HX HY ωX ωY)
          (boundedBelow f HX HY ωX ωY hωX hωY)).obj K) := sorry

/-- The new upper-shriek functor defined by duality with chosen dualizing complexes. -/
noncomputable def functor {X Y : Scheme.{u}} (f : X ⟶ Y) [FiniteType f]
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [BraidedCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    [MonoidalCategory (RingedSpace.ModuleDerived Y.toRingedSpace)]
    [BraidedCategory (RingedSpace.ModuleDerived Y.toRingedSpace)]
    (HY : MonoidalClosed (RingedSpace.ModuleDerived Y.toRingedSpace))
    (ωX : RingedSpace.ModuleDerived X.toRingedSpace)
    (ωY : RingedSpace.ModuleDerived Y.toRingedSpace)
    (hωX : RingedSpace.ModuleDerived.IsDualizingComplex ωX HX)
    (hωY : RingedSpace.ModuleDerived.IsDualizingComplex ωY HY) :
    D⁺[SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf] ⥤
      D⁺[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf] :=
  (DerivedCategory.Plus.cohomologyIn
    (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf)).lift
      ((t.plus : ObjectProperty
        (RingedSpace.ModuleDerived X.toRingedSpace)).lift
          (ambient f HX HY ωX ωY)
          (boundedBelow f HX HY ωX ωY hωX hωY))
      (coherent f HX HY ωX ωY hωX hωY)

/-- Forgetting boundedness and coherent cohomology recovers the ambient
duality-pullback-duality formula. -/
theorem functor_obj_obj {X Y : Scheme.{u}} (f : X ⟶ Y) [FiniteType f]
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [BraidedCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    [MonoidalCategory (RingedSpace.ModuleDerived Y.toRingedSpace)]
    [BraidedCategory (RingedSpace.ModuleDerived Y.toRingedSpace)]
    (HY : MonoidalClosed (RingedSpace.ModuleDerived Y.toRingedSpace))
    (ωX : RingedSpace.ModuleDerived X.toRingedSpace)
    (ωY : RingedSpace.ModuleDerived Y.toRingedSpace)
    (hωX : RingedSpace.ModuleDerived.IsDualizingComplex ωX HX)
    (hωY : RingedSpace.ModuleDerived.IsDualizingComplex ωY HY)
    (K : D⁺[SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf]) :
    ((functor f HX HY ωX ωY hωX hωY).obj K).obj.obj =
      (ambient f HX HY ωX ωY).obj K := sorry

/-- For a finite-type morphism between schemes of finite type over a Noetherian base,
the new upper-shriek functor is independent up to isomorphism of the base dualizing complex
and of the relatively normalized source and target dualizing complexes. -/
theorem functor_isIsomorphic
    {S : Scheme.{u}} [IsNoetherian S] {X Y : Scheme.FiniteTypeOver S} (f : X ⟶ Y) :
    let X' : Scheme := X.obj.left
    let Y' : Scheme := Y.obj.left
    let f' : X' ⟶ Y' := f.hom.left
    ∀ [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
      [BraidedCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
      (HS : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace))
      [MonoidalCategory (RingedSpace.ModuleDerived X'.toRingedSpace)]
      [BraidedCategory (RingedSpace.ModuleDerived X'.toRingedSpace)]
      (HX : MonoidalClosed (RingedSpace.ModuleDerived X'.toRingedSpace))
      [MonoidalCategory (RingedSpace.ModuleDerived Y'.toRingedSpace)]
      [BraidedCategory (RingedSpace.ModuleDerived Y'.toRingedSpace)]
      (HY : MonoidalClosed (RingedSpace.ModuleDerived Y'.toRingedSpace))
      (ωS ωS' : RingedSpace.ModuleDerived S.toRingedSpace)
      (hωS : ωS.IsDualizingComplex HS) (hωS' : ωS'.IsDualizingComplex HS)
      (ωX ωX' : RingedSpace.ModuleDerived X'.toRingedSpace)
      (ωY ωY' : RingedSpace.ModuleDerived Y'.toRingedSpace)
      (hX : @NormalizedDualizingComplex.RelativeTo _ _ _ X.obj.hom
        (FiniteTypeOver.instFiniteType X) _ HS _ HX ωS hωS ωX)
      (hX' : @NormalizedDualizingComplex.RelativeTo _ _ _ X.obj.hom
        (FiniteTypeOver.instFiniteType X) _ HS _ HX ωS' hωS' ωX')
      (hY : @NormalizedDualizingComplex.RelativeTo _ _ _ Y.obj.hom
        (FiniteTypeOver.instFiniteType Y) _ HS _ HY ωS hωS ωY)
      (hY' : @NormalizedDualizingComplex.RelativeTo _ _ _ Y.obj.hom
        (FiniteTypeOver.instFiniteType Y) _ HS _ HY ωS' hωS' ωY'),
      IsIsomorphic
        (@functor _ _ f' (FiniteTypeOver.instFiniteTypeHom f) _ _ HX _ _ HY ωX ωY
          (@NormalizedDualizingComplex.RelativeTo.isDualizing _ _ _ X.obj.hom
            (FiniteTypeOver.instFiniteType X) _ HS _ HX ωS hωS ωX hX)
          (@NormalizedDualizingComplex.RelativeTo.isDualizing _ _ _ Y.obj.hom
            (FiniteTypeOver.instFiniteType Y) _ HS _ HY ωS hωS ωY hY))
        (@functor _ _ f' (FiniteTypeOver.instFiniteTypeHom f) _ _ HX _ _ HY ωX' ωY'
          (@NormalizedDualizingComplex.RelativeTo.isDualizing _ _ _ X.obj.hom
            (FiniteTypeOver.instFiniteType X) _ HS _ HX ωS' hωS' ωX' hX')
          (@NormalizedDualizingComplex.RelativeTo.isDualizing _ _ _ Y.obj.hom
            (FiniteTypeOver.instFiniteType Y) _ HS _ HY ωS' hωS' ωY' hY')) := sorry

end AlgebraicGeometry.Scheme.Hom.NewUpperShriek
