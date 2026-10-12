/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.NormalizedDualizing.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.NormalizationDegree

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex.RelativeTo

open RingedSpace.ModuleDerived

/-- For a finite-type morphism over a Noetherian scheme, relative normalization identifies
the stalk normalization-degree function with the relative dimension function. -/
theorem stalkNormalizationDegree_eq_relativeDimensionFunction
    {S X : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [FiniteType f]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    (HS : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace))
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (ωS : RingedSpace.ModuleDerived S.toRingedSpace) (hωS : ωS.IsDualizingComplex HS)
    (ωX : RingedSpace.ModuleDerived X.toRingedSpace)
    (hωX : RelativeTo f HS HX ωS hωS ωX)
    (δS : S → ℤ) [IsDimensionFunction δS]
    (hδS : Scheme.IsDualizingComplex.IsStalkNormalizationDegreeFunction ωS δS)
    (δX : X → ℤ) [IsDimensionFunction δX]
    (hδX : @Scheme.IsDualizingComplex.IsStalkNormalizationDegreeFunction X
      (FiniteType.isNoetherian f).toIsLocallyNoetherian ωX δX) :
    δX = f.relativeDimensionFunction δS := sorry

/-- At each point of a finite-type morphism, the difference of relative stalk
normalization degrees equals the residue-field transcendence degree. -/
theorem normalizationDegree_sub_eq_residueFieldTrdegAt
    {S X : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [FiniteType f]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    (HS : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace))
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (ωS : RingedSpace.ModuleDerived S.toRingedSpace) (hωS : ωS.IsDualizingComplex HS)
    (ωX : RingedSpace.ModuleDerived X.toRingedSpace)
    (hωX : RelativeTo f HS HX ωS hωS ωX)
    (δS : S → ℤ) [IsDimensionFunction δS]
    (hδS : Scheme.IsDualizingComplex.IsStalkNormalizationDegreeFunction ωS δS)
    (δX : X → ℤ) [IsDimensionFunction δX]
    (hδX : @Scheme.IsDualizingComplex.IsStalkNormalizationDegreeFunction X
      (FiniteType.isNoetherian f).toIsLocallyNoetherian ωX δX)
    (x : X) :
    δX x - δS (f x) = (f.residueFieldTrdegAt x : ℤ) := sorry

end AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex.RelativeTo
