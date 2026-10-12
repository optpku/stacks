/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Factorization

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.ModuleDerived
open scoped DerivedCategory.CohomologyIn MonoidalCategory

noncomputable section

universe u

/- Remark 48.23.4 - relative dualizing factorization for Cohen–Macaulay morphisms. -/
@[stacks 0C10]
#check (AlgebraicGeometry.Scheme.UpperShriekAssignment.map_isIsomorphic_pullbackTensor :
  ∀ {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (d : ℕ)
    [AlgebraicGeometry.CohenMacaulay f.hom.left]
    [Scheme.Hom.RelativeDimension f.hom.left d]
    (E : Scheme.UpperShriekAssignment S)
    [MonoidalCategory (ModuleDerived (X.obj.left).toRingedSpace)]
    (K : DerivedQCoh.Plus Y.obj.left),
    let ωXY := cohomologySheaf
      (((E.map f).obj (DerivedQCoh.structureSheafPlus Y.obj.left)).obj.obj) (-(d : ℤ))
    IsIsomorphic ((E.map f).obj K).obj.obj
      ((modulePullbackDerived (f.hom.left).toShHom).obj K.obj.obj ⊗
        ((DerivedCategory.singleFunctor (X.obj.left).Modules 0).obj ωXY)⟦(d : ℤ)⟧))

/- Remark 48.23.4 - normalized dualizing complexes under relative factorization. -/
@[stacks 0C10]
#check (AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex.RelativeTo.isIsomorphic_pullbackTensorShift_of_cohenMacaulay :
  ∀ {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (d : ℕ)
    [AlgebraicGeometry.CohenMacaulay f.hom.left]
    [Scheme.Hom.RelativeDimension f.hom.left d]
    (E : Scheme.UpperShriekAssignment S)
    [MonoidalCategory (ModuleDerived S.toRingedSpace)]
    (HS : MonoidalClosed (ModuleDerived S.toRingedSpace))
    [MonoidalCategory (ModuleDerived (X.obj.left).toRingedSpace)]
    (HX : MonoidalClosed (ModuleDerived (X.obj.left).toRingedSpace))
    [MonoidalCategory (ModuleDerived (Y.obj.left).toRingedSpace)]
    (HY : MonoidalClosed (ModuleDerived (Y.obj.left).toRingedSpace))
    (ωS : ModuleDerived S.toRingedSpace) (hωS : ωS.IsDualizingComplex HS)
    (ωX : ModuleDerived (X.obj.left).toRingedSpace)
    (ωY : ModuleDerived (Y.obj.left).toRingedSpace)
    (hX : Scheme.Hom.NormalizedDualizingComplex.RelativeTo X.obj.hom HS HX ωS hωS ωX)
    (hY : Scheme.Hom.NormalizedDualizingComplex.RelativeTo Y.obj.hom HS HY ωS hωS ωY),
    let ωXY := cohomologySheaf
      (((E.map f).obj (DerivedQCoh.structureSheafPlus Y.obj.left)).obj.obj) (-(d : ℤ))
    IsIsomorphic ωX
      ((modulePullbackDerived (f.hom.left).toShHom).obj ωY ⊗
        ((DerivedCategory.singleFunctor (X.obj.left).Modules 0).obj ωXY)⟦(d : ℤ)⟧))

/- Remark 48.23.4 - canonical modules of connected Cohen–Macaulay schemes. -/
@[stacks 0C10]
#check (AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex.RelativeTo.dualizingModule_isIsomorphic_pullbackTensor :
  ∀ {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (d : ℕ)
    [AlgebraicGeometry.CohenMacaulay f.hom.left]
    [Scheme.Hom.RelativeDimension f.hom.left d]
    [ConnectedSpace X.obj.left] [Scheme.CohenMacaulay X.obj.left]
    [ConnectedSpace Y.obj.left] [Scheme.CohenMacaulay Y.obj.left]
    (E : Scheme.UpperShriekAssignment S)
    [MonoidalCategory (ModuleDerived S.toRingedSpace)]
    (HS : MonoidalClosed (ModuleDerived S.toRingedSpace))
    [MonoidalCategory (ModuleDerived (X.obj.left).toRingedSpace)]
    (HX : MonoidalClosed (ModuleDerived (X.obj.left).toRingedSpace))
    [MonoidalCategory (ModuleDerived (Y.obj.left).toRingedSpace)]
    (HY : MonoidalClosed (ModuleDerived (Y.obj.left).toRingedSpace))
    (ωS : ModuleDerived S.toRingedSpace) (hωS : ωS.IsDualizingComplex HS)
    (KX : ModuleDerived (X.obj.left).toRingedSpace)
    (KY : ModuleDerived (Y.obj.left).toRingedSpace)
    (hX : Scheme.Hom.NormalizedDualizingComplex.RelativeTo X.obj.hom HS HX ωS hωS KX)
    (hY : Scheme.Hom.NormalizedDualizingComplex.RelativeTo Y.obj.hom HS HY ωS hωS KY)
    (nX nY : ℤ)
    (hKX : Nonempty (KX ≅
      ((DerivedCategory.singleFunctor (X.obj.left).Modules 0).obj (cohomologySheaf KX nX))
        ⟦-nX⟧))
    (hKY : Nonempty (KY ≅
      ((DerivedCategory.singleFunctor (Y.obj.left).Modules 0).obj (cohomologySheaf KY nY))
        ⟦-nY⟧)),
    let ωX := cohomologySheaf KX nX
    let ωY := cohomologySheaf KY nY
    let ωXY := cohomologySheaf
      (((E.map f).obj (DerivedQCoh.structureSheafPlus Y.obj.left)).obj.obj) (-(d : ℤ))
    IsIsomorphic ωX ((Modules.pullback f.hom.left).obj ωY ⊗ ωXY))

/- Remark 48.23.4 - the finite-type nonseparated analogue for new upper shriek. -/
@[stacks 0C10]
#check (AlgebraicGeometry.Scheme.Hom.NewUpperShriek.map_isIsomorphic_pullbackTensor :
  ∀ {S : Scheme.{u}} [IsNoetherian S]
    [MonoidalCategory (ModuleDerived S.toRingedSpace)]
    (HS : MonoidalClosed (ModuleDerived S.toRingedSpace))
    (ωS : ModuleDerived S.toRingedSpace) (hωS : ωS.IsDualizingComplex HS)
    {X Y : FiniteTypeOver S} (f : X ⟶ Y) (d : ℕ)
    [AlgebraicGeometry.CohenMacaulay f.hom.left]
    [Scheme.Hom.RelativeDimension f.hom.left d]
    [MonoidalCategory (ModuleDerived (X.obj.left).toRingedSpace)]
    [BraidedCategory (ModuleDerived (X.obj.left).toRingedSpace)]
    (HX : MonoidalClosed (ModuleDerived (X.obj.left).toRingedSpace))
    [MonoidalCategory (ModuleDerived (Y.obj.left).toRingedSpace)]
    [BraidedCategory (ModuleDerived (Y.obj.left).toRingedSpace)]
    (HY : MonoidalClosed (ModuleDerived (Y.obj.left).toRingedSpace))
    (ωX : D⁺[SheafOfModules.isCoherent (X.obj.left).toRingedSpace.ringCatSheaf])
    (ωY : D⁺[SheafOfModules.isCoherent (Y.obj.left).toRingedSpace.ringCatSheaf])
    (hX : @Scheme.Hom.NormalizedDualizingComplex.RelativeTo _ _ _ X.obj.hom
      (FiniteTypeOver.instFiniteType X) _ HS _ HX ωS hωS ωX.obj.obj)
    (hY : @Scheme.Hom.NormalizedDualizingComplex.RelativeTo _ _ _ Y.obj.hom
      (FiniteTypeOver.instFiniteType Y) _ HS _ HY ωS hωS ωY.obj.obj)
    (OY : D⁺[SheafOfModules.isCoherent (Y.obj.left).toRingedSpace.ringCatSheaf])
    (hOY : IsIsomorphic OY.obj.obj (DerivedQCoh.structureSheaf Y.obj.left).obj)
    (K : D⁺[SheafOfModules.isCoherent (Y.obj.left).toRingedSpace.ringCatSheaf]),
    let fShriek := @Scheme.Hom.NewUpperShriek.functor _ _ f.hom.left
      (FiniteTypeOver.instFiniteTypeHom f) _ _ HX _ _ HY ωX.obj.obj ωY.obj.obj
      (@Scheme.Hom.NormalizedDualizingComplex.RelativeTo.isDualizing _ _ _ X.obj.hom
        (FiniteTypeOver.instFiniteType X) _ HS _ HX ωS hωS ωX.obj.obj hX)
      (@Scheme.Hom.NormalizedDualizingComplex.RelativeTo.isDualizing _ _ _ Y.obj.hom
        (FiniteTypeOver.instFiniteType Y) _ HS _ HY ωS hωS ωY.obj.obj hY)
    let ωXY := cohomologySheaf ((fShriek.obj OY).obj.obj) (-(d : ℤ))
    IsIsomorphic (fShriek.obj K).obj.obj
      ((modulePullbackDerived (f.hom.left).toShHom).obj K.obj.obj ⊗
        ((DerivedCategory.singleFunctor (X.obj.left).Modules 0).obj ωXY)⟦(d : ℤ)⟧))
