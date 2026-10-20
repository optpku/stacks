module

public import ReasLib.AlgebraicGeometry.Scheme.Model.Regular.Contraction

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Contraction steps retain the exceptional curve and the two model compatibilities. -/
#check (AlgebraicGeometry.Scheme.Hom.ContractionStep :
  ∀ {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    (source target : RegularModel R K C), Type u)

/- The explicit constructor preserves the morphism, exceptional curve, and compatibility laws. -/
#check (AlgebraicGeometry.Scheme.Hom.ContractionStep.ofData :
  ∀ {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    {source target : RegularModel R K C} (morphism : source.scheme ⟶ target.scheme)
    (exceptionalIdeal : source.scheme.IdealSheafData)
    (h_exceptional : IsExceptionalCurveFirstKind exceptionalIdeal)
    (center : closedPoints target.scheme)
    (h_contraction : @IsContraction source.scheme target.scheme source.isNoetherian
      exceptionalIdeal h_exceptional morphism center)
    (h_over : morphism ≫ target.base = source.base)
    (h_genericFiber :
      source.genericFiberIso.hom ≫
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map
            (Over.homMk morphism h_over : Over.mk source.base ⟶ Over.mk target.base) =
        target.genericFiberIso.hom), ContractionStep source target)

end AlgebraicGeometry.Scheme.Hom
