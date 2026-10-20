module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.PointwiseIntegral
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/- Definition 33.9.1: geometric pointwise integrality at a point. -/
@[stacks 020H] #check
  (AlgebraicGeometry.Scheme.Hom.isGeometricallyPointwiseIntegralAt_iff (f := f) :
    ∀ x : X,
      AlgebraicGeometry.Scheme.Hom.IsGeometricallyPointwiseIntegralAt f x ↔
        ∀ (K : Type u) [Field K] [Algebra k K],
          ∀ x' : FieldExtension.baseChange k K f,
            FieldExtension.toSource k K f x' = x →
              IsDomain ((FieldExtension.baseChange k K f).presheaf.stalk x'))

#check
  (AlgebraicGeometry.Scheme.Hom.isGeometricallyPointwiseIntegral_iff (f := f) :
    AlgebraicGeometry.Scheme.Hom.IsGeometricallyPointwiseIntegral f ↔
      ∀ x : X, AlgebraicGeometry.Scheme.Hom.IsGeometricallyPointwiseIntegralAt f x)

#check
  (AlgebraicGeometry.Scheme.Hom.geometricallyIntegral_iff_forall_isIntegral_pullback (f := f) :
    GeometricallyIntegral f ↔
      ∀ (K : Type u) [Field K] [Algebra k K],
        IsIntegral (FieldExtension.baseChange k K f))
