module

public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.GeometricGenus

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.NonsingularProjectiveModel.WithIso

#check
  (AlgebraicGeometry.NonsingularProjectiveModel.WithIso.genus :
    ∀ {k : Type u} [Field k] {X : SchemeOverField k} [Curve X] (Y : WithIso X), ℕ)

#check
  (AlgebraicGeometry.NonsingularProjectiveModel.WithIso.genus_def :
    ∀ {k : Type u} [Field k] {X : SchemeOverField k} [Curve X] (Y : WithIso X),
    Y.genus = Scheme.Hom.cohomologyFinrank Y.curve.hom
      (SheafOfModules.unit Y.curve.left.ringCatSheaf : Y.curve.left.Modules) 1)

#check
  (AlgebraicGeometry.NonsingularProjectiveModel.WithIso.genus_eq_curveGenus :
    ∀ {k : Type u} [Field k] {X : SchemeOverField k} [Curve X]
    (Y : WithIso X) [Smooth Y.curve.hom] [GeometricallyIrreducible Y.curve.hom],
    Y.genus = @Curve.genus k _ Y.curve Y.isCurve Y.projective _ _)

end AlgebraicGeometry.NonsingularProjectiveModel.WithIso

namespace AlgebraicGeometry.Curve

#check
  (AlgebraicGeometry.Curve.geometricGenus :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [GeometricallyIrreducible X.hom], ℕ)

#check
  (AlgebraicGeometry.Curve.geometricGenus_eq_modelGenus :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    (X : SchemeOverField k) [Curve X] [GeometricallyIrreducible X.hom]
    (Y : NonsingularProjectiveModel.WithIso
      (FieldExtension.Reduced.baseChange k K X)) [Smooth Y.curve.hom],
    geometricGenus X = Y.genus)

#check
  (AlgebraicGeometry.Curve.exists_geometricGenusModel :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [GeometricallyIrreducible X.hom],
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K)
      (_ : FiniteDimensional k K) (_ : IsPurelyInseparable k K)
      (Y : NonsingularProjectiveModel.WithIso
        (FieldExtension.Reduced.baseChange k K X)),
      Smooth Y.curve.hom ∧ geometricGenus X = Y.genus)

#check
  (AlgebraicGeometry.Curve.geometricGenus_eq_genus :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [GeometricallyIrreducible X.hom] [Smooth X.hom] [Projective X.hom],
    geometricGenus X = genus X)

end AlgebraicGeometry.Curve
