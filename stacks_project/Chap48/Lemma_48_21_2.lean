/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.NormalizedDualizing.DimensionFunction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 48.21.2 -/
@[stacks 0AWM] #check
  (AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex.RelativeTo.normalizationDegree_sub_eq_residueFieldTrdegAt :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsNoetherian S]
      (f : X ⟶ S) [Scheme.Hom.FiniteType f]
      [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
      (HS : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace))
      [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
      (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
      (ωS : RingedSpace.ModuleDerived S.toRingedSpace)
      (hωS : ωS.IsDualizingComplex HS)
      (ωX : RingedSpace.ModuleDerived X.toRingedSpace)
      (hωX : Scheme.Hom.NormalizedDualizingComplex.RelativeTo f HS HX ωS hωS ωX)
      (δS : S → ℤ) [IsDimensionFunction δS]
      (hδS : Scheme.IsDualizingComplex.IsStalkNormalizationDegreeFunction ωS δS)
      (δX : X → ℤ) [IsDimensionFunction δX]
      (hδX : @Scheme.IsDualizingComplex.IsStalkNormalizationDegreeFunction X
        (Scheme.Hom.FiniteType.isNoetherian f).toIsLocallyNoetherian ωX δX)
      (x : X),
      δX x - δS (f x) = (f.residueFieldTrdegAt x : ℤ))
