module

public import ReasLib.AlgebraicGeometry.Scheme.K0.Comparison

universe u

#check
  (AlgebraicGeometry.Scheme.K0'.derivedK0Equiv :
    (Y : AlgebraicGeometry.Scheme.{u}) →
      [AlgebraicGeometry.IsLocallyNoetherian Y] →
        AlgebraicGeometry.Scheme.K0' Y ≃+
          CategoryTheory.TriangulatedK0
            (CategoryTheory.DerivedCategory.Bounded.CohomologyIn
              (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf)))
