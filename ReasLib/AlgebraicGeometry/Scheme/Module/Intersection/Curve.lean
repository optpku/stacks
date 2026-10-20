module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.IdealSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.SmoothSurface
public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.Number

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.Intersection

/-- The intersection number of two integral curves on an integral smooth proper surface is
the degree of the line bundle associated to the first curve along the second curve. -/
noncomputable def curveNumber
    {k : Type u} [Field k] (S : SchemeOverField k)
    [IsProper S.hom] [Smooth S.hom] [IsIntegral S.left]
    (hSdim : topologicalKrullDim S.left = 2)
    (C D : S.left.IdealSheafData)
    [IsIntegral C.subscheme] [IsIntegral D.subscheme]
    (hCdim : topologicalKrullDim C.subscheme = 1)
    (hDdim : topologicalKrullDim D.subscheme = 1) : ℚ :=
  @lineNumber k _ S.left S.hom _ D inferInstance
    (@Scheme.IdealSheafData.associatedSheaf S.left C
      (Scheme.IdealSheafData.isEffectiveCartierDivisor_of_smoothSurface S hSdim C hCdim))
    (@Scheme.effectiveCartierDivisorAssociatedSheaf_isInvertible S.left inferInstance
      C.toSubobject
      (Scheme.IdealSheafData.effectiveCartierIdealFact C
        (Scheme.IdealSheafData.isEffectiveCartierDivisor_of_smoothSurface S hSdim C hCdim)))

/-- The intersection number of two curves is the one-factor intersection coefficient of the
line bundle associated to the first curve restricted to the second. -/
theorem curveNumber_def
    {k : Type u} [Field k] (S : SchemeOverField k)
    [IsProper S.hom] [Smooth S.hom] [IsIntegral S.left]
    (hSdim : topologicalKrullDim S.left = 2)
    (C D : S.left.IdealSheafData)
    [IsIntegral C.subscheme] [IsIntegral D.subscheme]
    (hCdim : topologicalKrullDim C.subscheme = 1)
    (hDdim : topologicalKrullDim D.subscheme = 1) :
    curveNumber S hSdim C D hCdim hDdim =
      @lineNumber k _ S.left S.hom _ D inferInstance
        (@Scheme.IdealSheafData.associatedSheaf S.left C
          (Scheme.IdealSheafData.isEffectiveCartierDivisor_of_smoothSurface S hSdim C hCdim))
        (@Scheme.effectiveCartierDivisorAssociatedSheaf_isInvertible S.left inferInstance
          C.toSubobject
          (Scheme.IdealSheafData.effectiveCartierIdealFact C
            (Scheme.IdealSheafData.isEffectiveCartierDivisor_of_smoothSurface S hSdim C hCdim))) := sorry

end AlgebraicGeometry.Scheme.Modules.Intersection
