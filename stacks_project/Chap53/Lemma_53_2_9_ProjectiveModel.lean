module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Reduced
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.OpenSubschemes
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A nonsingular projective model of a curve over a field is a regular projective curve
birational over that field to the given curve. -/
structure NonsingularProjectiveModel {k : Type u} [Field k]
    (X : SchemeOverField k) where
  /-- The projective curve underlying the model. -/
  curve : SchemeOverField k
  /-- The underlying model is a curve. -/
  isCurve : Curve curve
  /-- Nonsingularity is expressed as regularity of the underlying scheme. -/
  regular : Scheme.Regular curve.left
  /-- The model is projective over its ground field. -/
  projective : Projective curve.hom
  /-- The model and the given curve contain isomorphic nonempty opens over the ground field. -/
  birational : HasIsomorphicNonemptyOpenSubschemesOver
    (Spec (CommRingCat.of k)) X.left curve.left

namespace NonsingularProjectiveModel

/-- Build a nonsingular projective model from an explicit regular projective curve and a
birational identification over the ground field. -/
def of {k : Type u} [Field k] (X Y : SchemeOverField k)
    (h_curve : Curve Y) (h_regular : Scheme.Regular Y.left)
    (h_projective : Projective Y.hom)
    (h_birational : HasIsomorphicNonemptyOpenSubschemesOver
      (Spec (CommRingCat.of k)) X.left Y.left) :
    NonsingularProjectiveModel X where
  curve := Y
  isCurve := h_curve
  regular := h_regular
  projective := h_projective
  birational := h_birational

end NonsingularProjectiveModel

end AlgebraicGeometry
