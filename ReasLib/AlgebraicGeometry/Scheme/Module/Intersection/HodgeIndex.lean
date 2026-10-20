module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Family
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample
public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.Whole
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Properties
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Intersection

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- On a smooth projective surface, an invertible module with vanishing intersection
against an ample invertible module has nonpositive self-intersection. -/
@[stacks 0ELH]
theorem hodgeIndex
    {k : Type u} [Field k] (X : SchemeOverField k)
    [ProjectiveVariety X] [SmoothOfRelativeDimension 2 X.hom]
    (hXdim : topologicalKrullDim X.left = 2)
    [HasExt (Sheaf (Opens.grothendieckTopology
      (⊥ : X.left.IdealSheafData).subscheme.carrier) AddCommGrpCat.{u})]
    (H D : X.left.Modules) [Invertible H] [Invertible D] [IsAmple H]
    (hHD : number k X.hom (⊥ : X.left.IdealSheafData)
      (topologicalKrullDim_bot_eq X.left hXdim) ![H, D] = 0) :
    selfNumber k X.hom (⊥ : X.left.IdealSheafData)
      (topologicalKrullDim_bot_eq X.left hXdim) D ≤ 0 := sorry

end AlgebraicGeometry.SchemeOverField
