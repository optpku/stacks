module

public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent.AffineComparison.Derived
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.Affine
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import ReasLib.RingTheory.Extension.Cotangent.Surjective

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.NaiveCotangent

/-- For an immersion of schemes, the naive cotangent complex is isomorphic in the derived
category to the conormal sheaf placed in degree zero and shifted by one. -/
theorem isomorphicConormalShift {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] :
    IsIsomorphic
      (DerivedCategory.Q.obj (AlgebraicGeometry.Scheme.Hom.naiveCotangent i))
      ((shiftFunctor (DerivedCategory Z.Modules) (1 : ℤ)).obj
        ((DerivedCategory.singleFunctor Z.Modules (0 : ℤ)).obj
          (AlgebraicGeometry.Scheme.Hom.conormalSheaf i))) := sorry

end AlgebraicGeometry.Scheme.Hom.NaiveCotangent
