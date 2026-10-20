module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.Pseudofunctor
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.CohenMacaulay
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.NormalizedDualizing.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.CohenMacaulay
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.NewUpperShriek

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.ModuleDerived
open scoped DerivedCategory.CohomologyIn MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace UpperShriekAssignment

/-- For a Cohen–Macaulay morphism of relative dimension `d`, the selected upper-shriek
image is the derived pullback of a complex tensored with the relative dualizing sheaf
and shifted by `d`. -/
theorem map_isIsomorphic_pullbackTensor
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (d : ℕ)
    [AlgebraicGeometry.CohenMacaulay f.hom.left]
    [Hom.RelativeDimension f.hom.left d]
    (E : UpperShriekAssignment S)
    [MonoidalCategory (ModuleDerived (X.obj.left).toRingedSpace)]
    (K : DerivedQCoh.Plus Y.obj.left) :
    let ωXY := cohomologySheaf
      (((E.map f).obj (DerivedQCoh.structureSheafPlus Y.obj.left)).obj.obj) (-(d : ℤ))
    IsIsomorphic ((E.map f).obj K).obj.obj
      ((modulePullbackDerived (f.hom.left).toShHom).obj K.obj.obj ⊗
        ((DerivedCategory.singleFunctor (X.obj.left).Modules 0).obj ωXY)⟦(d : ℤ)⟧) := sorry

end UpperShriekAssignment

namespace Hom
namespace NormalizedDualizingComplex
namespace RelativeTo

/-- For relatively normalized dualizing complexes and a Cohen–Macaulay morphism of relative
dimension `d`, the source complex is the derived pullback of the target complex tensored
with the relative dualizing sheaf and shifted by `d`. -/
theorem isIsomorphic_pullbackTensorShift_of_cohenMacaulay
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (d : ℕ)
    [AlgebraicGeometry.CohenMacaulay f.hom.left]
    [Hom.RelativeDimension f.hom.left d]
    (E : UpperShriekAssignment S)
    [MonoidalCategory (ModuleDerived S.toRingedSpace)]
    (HS : MonoidalClosed (ModuleDerived S.toRingedSpace))
    [MonoidalCategory (ModuleDerived (X.obj.left).toRingedSpace)]
    (HX : MonoidalClosed (ModuleDerived (X.obj.left).toRingedSpace))
    [MonoidalCategory (ModuleDerived (Y.obj.left).toRingedSpace)]
    (HY : MonoidalClosed (ModuleDerived (Y.obj.left).toRingedSpace))
    (ωS : ModuleDerived S.toRingedSpace) (hωS : ωS.IsDualizingComplex HS)
    (ωX : ModuleDerived (X.obj.left).toRingedSpace)
    (ωY : ModuleDerived (Y.obj.left).toRingedSpace)
    (hX : RelativeTo X.obj.hom HS HX ωS hωS ωX)
    (hY : RelativeTo Y.obj.hom HS HY ωS hωS ωY) :
    let ωXY := cohomologySheaf
      (((E.map f).obj (DerivedQCoh.structureSheafPlus Y.obj.left)).obj.obj) (-(d : ℤ))
    IsIsomorphic ωX
      ((modulePullbackDerived (f.hom.left).toShHom).obj ωY ⊗
        ((DerivedCategory.singleFunctor (X.obj.left).Modules 0).obj ωXY)⟦(d : ℤ)⟧) := sorry

/-- For connected Cohen–Macaulay source and target schemes, the specified nonzero
cohomology modules of normalized dualizing complexes satisfy the canonical-module
pullback–tensor isomorphism. -/
theorem dualizingModule_isIsomorphic_pullbackTensor
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (d : ℕ)
    [AlgebraicGeometry.CohenMacaulay f.hom.left]
    [Hom.RelativeDimension f.hom.left d]
    [ConnectedSpace X.obj.left] [Scheme.CohenMacaulay X.obj.left]
    [ConnectedSpace Y.obj.left] [Scheme.CohenMacaulay Y.obj.left]
    (E : UpperShriekAssignment S)
    [MonoidalCategory (ModuleDerived S.toRingedSpace)]
    (HS : MonoidalClosed (ModuleDerived S.toRingedSpace))
    [MonoidalCategory (ModuleDerived (X.obj.left).toRingedSpace)]
    (HX : MonoidalClosed (ModuleDerived (X.obj.left).toRingedSpace))
    [MonoidalCategory (ModuleDerived (Y.obj.left).toRingedSpace)]
    (HY : MonoidalClosed (ModuleDerived (Y.obj.left).toRingedSpace))
    (ωS : ModuleDerived S.toRingedSpace) (hωS : ωS.IsDualizingComplex HS)
    (KX : ModuleDerived (X.obj.left).toRingedSpace)
    (KY : ModuleDerived (Y.obj.left).toRingedSpace)
    (hX : RelativeTo X.obj.hom HS HX ωS hωS KX)
    (hY : RelativeTo Y.obj.hom HS HY ωS hωS KY)
    (nX nY : ℤ)
    (hKX : Nonempty (KX ≅
      ((DerivedCategory.singleFunctor (X.obj.left).Modules 0).obj (cohomologySheaf KX nX))
        ⟦-nX⟧))
    (hKY : Nonempty (KY ≅
      ((DerivedCategory.singleFunctor (Y.obj.left).Modules 0).obj (cohomologySheaf KY nY))
        ⟦-nY⟧)) :
    let ωX := cohomologySheaf KX nX
    let ωY := cohomologySheaf KY nY
    let ωXY := cohomologySheaf
      (((E.map f).obj (DerivedQCoh.structureSheafPlus Y.obj.left)).obj.obj) (-(d : ℤ))
    IsIsomorphic ωX ((Modules.pullback f.hom.left).obj ωY ⊗ ωXY) := sorry

end RelativeTo
end NormalizedDualizingComplex

namespace NewUpperShriek

/-- For finite-type schemes over a Noetherian base, the normalized new upper-shriek
functor satisfies the relative dualizing pullback–tensor formula. -/
theorem map_isIsomorphic_pullbackTensor
    {S : Scheme.{u}} [IsNoetherian S]
    [MonoidalCategory (ModuleDerived S.toRingedSpace)]
    (HS : MonoidalClosed (ModuleDerived S.toRingedSpace))
    (ωS : ModuleDerived S.toRingedSpace) (hωS : ωS.IsDualizingComplex HS)
    {X Y : FiniteTypeOver S} (f : X ⟶ Y) (d : ℕ)
    [AlgebraicGeometry.CohenMacaulay f.hom.left]
    [Hom.RelativeDimension f.hom.left d]
    [MonoidalCategory (ModuleDerived (X.obj.left).toRingedSpace)]
    [BraidedCategory (ModuleDerived (X.obj.left).toRingedSpace)]
    (HX : MonoidalClosed (ModuleDerived (X.obj.left).toRingedSpace))
    [MonoidalCategory (ModuleDerived (Y.obj.left).toRingedSpace)]
    [BraidedCategory (ModuleDerived (Y.obj.left).toRingedSpace)]
    (HY : MonoidalClosed (ModuleDerived (Y.obj.left).toRingedSpace))
    (ωX : D⁺[SheafOfModules.isCoherent (X.obj.left).toRingedSpace.ringCatSheaf])
    (ωY : D⁺[SheafOfModules.isCoherent (Y.obj.left).toRingedSpace.ringCatSheaf])
    (hX : @NormalizedDualizingComplex.RelativeTo _ _ _ X.obj.hom
      (FiniteTypeOver.instFiniteType X) _ HS _ HX ωS hωS ωX.obj.obj)
    (hY : @NormalizedDualizingComplex.RelativeTo _ _ _ Y.obj.hom
      (FiniteTypeOver.instFiniteType Y) _ HS _ HY ωS hωS ωY.obj.obj)
    (OY : D⁺[SheafOfModules.isCoherent (Y.obj.left).toRingedSpace.ringCatSheaf])
    (hOY : IsIsomorphic OY.obj.obj (DerivedQCoh.structureSheaf Y.obj.left).obj)
    (K : D⁺[SheafOfModules.isCoherent (Y.obj.left).toRingedSpace.ringCatSheaf]) :
    let fShriek := @functor _ _ f.hom.left (FiniteTypeOver.instFiniteTypeHom f) _ _ HX _ _ HY
      ωX.obj.obj ωY.obj.obj
      (@NormalizedDualizingComplex.RelativeTo.isDualizing _ _ _ X.obj.hom
        (FiniteTypeOver.instFiniteType X) _ HS _ HX ωS hωS ωX.obj.obj hX)
      (@NormalizedDualizingComplex.RelativeTo.isDualizing _ _ _ Y.obj.hom
        (FiniteTypeOver.instFiniteType Y) _ HS _ HY ωS hωS ωY.obj.obj hY)
    let ωXY := cohomologySheaf ((fShriek.obj OY).obj.obj) (-(d : ℤ))
    IsIsomorphic (fShriek.obj K).obj.obj
      ((modulePullbackDerived (f.hom.left).toShHom).obj K.obj.obj ⊗
        ((DerivedCategory.singleFunctor (X.obj.left).Modules 0).obj ωXY)⟦(d : ℤ)⟧) := sorry

end NewUpperShriek
end Hom
end Scheme
end AlgebraicGeometry
