module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Stalk.Local
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Normal
public import ReasLib.RingTheory.Normal.GeometricallyNormal.FieldTests

/-!
# Pointwise purely inseparable tests for geometric normality

This module records a finite purely inseparable field-extension criterion for
geometric normality at a point of a scheme over a field.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- For a point of a scheme over a field, geometric normality at the point, normality of every
stalk above it after a finite purely inseparable field extension, and geometric normality of the
original stalk are equivalent. -/
@[stacks 038N]
theorem geometricallyNormalAt_tfae {k : Type u} [Field k]
    (X : Over (Spec (CommRingCat.of k))) (x : X.left) :
    List.TFAE
      [ geometricallyNormalAt X x
      , ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K]
          [IsPurelyInseparable k K],
          ∀ x' : FieldExtension.baseChange k K X.hom,
            FieldExtension.toSource k K X.hom x' = x →
              IsNormalRing ((FieldExtension.baseChange k K X.hom).presheaf.stalk x')
      , Algebra.IsGeometricallyNormal k (X.left.presheaf.stalk x)
      ] := sorry

end AlgebraicGeometry.SchemeOverField
