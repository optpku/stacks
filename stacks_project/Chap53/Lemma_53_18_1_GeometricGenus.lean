module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.GeometricGenus

@[expose] public section

open CategoryTheory

universe u

#check
  (AlgebraicGeometry.FieldExtension.Over.instIsProperBaseChange :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
      (X : AlgebraicGeometry.SchemeOverField k) [AlgebraicGeometry.IsProper X.hom],
      AlgebraicGeometry.IsProper
        (AlgebraicGeometry.FieldExtension.Over.baseChange k K X).hom)

#check
  (AlgebraicGeometry.SchemeOverField.oneDimensionalComponent :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      (Z : irreducibleComponents X.left)
      (_ : topologicalKrullDim
        (X.left.irreducibleComponentSubscheme Z) = 1),
      AlgebraicGeometry.SchemeOverField k)

#check
  (AlgebraicGeometry.SchemeOverField.oneDimensionalComponent_hom :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      (Z : irreducibleComponents X.left)
      (hZ : topologicalKrullDim
        (X.left.irreducibleComponentSubscheme Z) = 1),
      (AlgebraicGeometry.SchemeOverField.oneDimensionalComponent X Z hZ).hom =
        X.left.irreducibleComponentSubschemeι Z ≫ X.hom)

#check
  (AlgebraicGeometry.SchemeOverField.OneDimensionalComponent.instIsProper :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.IsProper X.hom]
      (Z : irreducibleComponents X.left)
      (hZ : topologicalKrullDim
        (X.left.irreducibleComponentSubscheme Z) = 1),
      AlgebraicGeometry.IsProper
        (AlgebraicGeometry.SchemeOverField.oneDimensionalComponent X Z hZ).hom)

#check
  (AlgebraicGeometry.SchemeOverField.OneDimensionalComponent.instCurve :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.IsProper X.hom]
      (Z : irreducibleComponents X.left)
      (hZ : topologicalKrullDim
        (X.left.irreducibleComponentSubscheme Z) = 1),
      AlgebraicGeometry.Curve
        (AlgebraicGeometry.SchemeOverField.oneDimensionalComponent X Z hZ))

#check
  (AlgebraicGeometry.SchemeOverField.OneDimensionalComponent.instGeometricallyIrreducible :
    ∀ {k : Type u} [Field k] [IsSepClosed k]
      (X : AlgebraicGeometry.SchemeOverField k)
      (Z : irreducibleComponents X.left)
      (hZ : topologicalKrullDim
        (X.left.irreducibleComponentSubscheme Z) = 1),
      AlgebraicGeometry.GeometricallyIrreducible
        (AlgebraicGeometry.SchemeOverField.oneDimensionalComponent X Z hZ).hom)

#check
  (AlgebraicGeometry.GeometricGenus.ofScheme :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.IsProper X.hom]
      (_ : topologicalKrullDim X.left ≤ 1), ℕ)

#check
  (AlgebraicGeometry.GeometricGenus.ofScheme_def :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.IsProper X.hom]
      (hdim : topologicalKrullDim X.left ≤ 1),
      AlgebraicGeometry.GeometricGenus.ofScheme X hdim =
        ∑ᶠ Z : irreducibleComponents
            (AlgebraicGeometry.FieldExtension.Over.baseChange k
              (AlgebraicClosure k) X).left,
          if hZ : topologicalKrullDim
              ((AlgebraicGeometry.FieldExtension.Over.baseChange k
                (AlgebraicClosure k) X).left.irreducibleComponentSubscheme Z) = 1 then
            AlgebraicGeometry.Curve.geometricGenus
              (AlgebraicGeometry.SchemeOverField.oneDimensionalComponent
                (AlgebraicGeometry.FieldExtension.Over.baseChange k
                  (AlgebraicClosure k) X) Z hZ)
          else 0)

#check
  (AlgebraicGeometry.GeometricGenus.ofScheme_eq_curve :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.Curve X] [AlgebraicGeometry.IsProper X.hom]
      [AlgebraicGeometry.GeometricallyIrreducible X.hom],
      AlgebraicGeometry.GeometricGenus.ofScheme X
          (AlgebraicGeometry.topologicalKrullDim_eq_one X).le =
        AlgebraicGeometry.Curve.geometricGenus X)

#check
  (AlgebraicGeometry.GeometricGenus.eq_finsum_irreducibleComponents :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.IsProper X.hom]
      (hdim : topologicalKrullDim X.left ≤ 1),
      AlgebraicGeometry.GeometricGenus.ofScheme X hdim =
        ∑ᶠ Z : irreducibleComponents X.left,
          if hZ : topologicalKrullDim
              (X.left.irreducibleComponentSubscheme Z) = 1 then
            AlgebraicGeometry.GeometricGenus.ofScheme
              (AlgebraicGeometry.SchemeOverField.oneDimensionalComponent X Z hZ) hZ.le
          else 0)
