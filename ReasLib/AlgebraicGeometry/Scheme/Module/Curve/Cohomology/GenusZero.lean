module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- An invertible module of degree zero on a proper genus-zero curve with only constant global
sections is isomorphic to the structure module. -/
theorem isoUnit_of_genus_zero_of_degree_zero
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X] [IsProper X.hom]
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_genus : Scheme.Hom.cohomologyFinrank X.hom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 = 0)
    (L : X.left.Modules) [Scheme.Modules.Invertible L]
    (h_degree : Scheme.Modules.curveDegreeOfInvertible X.hom
      (topologicalKrullDim_eq_one X).le L = 0) :
    Nonempty (L ≅ (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules)) := sorry

/-- A positive-degree invertible module on a proper genus-zero curve with only constant global
sections has global sections of dimension one more than its degree. -/
theorem cohomologyFinrank_zero_eq_degree_add_one_of_genus_zero
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X] [IsProper X.hom]
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_genus : Scheme.Hom.cohomologyFinrank X.hom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 = 0)
    (L : X.left.Modules) [Scheme.Modules.Invertible L] (d : ℕ)
    (h_degree : Scheme.Modules.curveDegreeOfInvertible X.hom
      (topologicalKrullDim_eq_one X).le L = (d : ℤ))
    (h_positive : 0 < d) :
    Scheme.Hom.cohomologyFinrank X.hom L 0 = d + 1 := sorry

/-- A positive-degree invertible module on a proper genus-zero curve with only constant global
sections has vanishing first cohomology. -/
theorem cohomologyFinrank_one_eq_zero_of_genus_zero
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X] [IsProper X.hom]
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_genus : Scheme.Hom.cohomologyFinrank X.hom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 = 0)
    (L : X.left.Modules) [Scheme.Modules.Invertible L] (d : ℕ)
    (h_degree : Scheme.Modules.curveDegreeOfInvertible X.hom
      (topologicalKrullDim_eq_one X).le L = (d : ℤ))
    (h_positive : 0 < d) :
    Scheme.Hom.cohomologyFinrank X.hom L 1 = 0 := sorry

end AlgebraicGeometry.SchemeOverField
