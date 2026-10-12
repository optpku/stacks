/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.Birational
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.NonsingularProjectiveModel

universe u

/-- A nonsingular projective model of a curve `X` over `k`, with a chosen isomorphism
from the function field of `X` to that of the model curve. -/
structure WithIso {k : Type u} [Field k] (X : SchemeOverField k) [Curve X] where
  /-- The nonsingular projective curve underlying the model. -/
  curve : SchemeOverField k
  /-- The underlying model is a curve. -/
  isCurve : Curve curve
  /-- Nonsingularity is expressed as regularity of the underlying scheme. -/
  regular : Scheme.Regular curve.left
  /-- The model is projective over its ground field. -/
  projective : Projective curve.hom
  /-- The chosen isomorphism `k(X) ≅ k(curve)` of function fields as `k`-algebras. -/
  functionFieldIso :
    SchemeOverField.functionFieldCommAlg X ≅
      @SchemeOverField.functionFieldCommAlg k _ curve isCurve.toVariety

namespace WithIso

/-- Build a model with chosen function-field isomorphism from explicit curve data. -/
def of {k : Type u} [Field k] (X Y : SchemeOverField k) [Curve X]
    (h_curve : Curve Y) (h_regular : Scheme.Regular Y.left)
    (h_projective : Projective Y.hom)
    (φ : SchemeOverField.functionFieldCommAlg X ≅
      @SchemeOverField.functionFieldCommAlg k _ Y h_curve.toVariety) :
    WithIso X where
  curve := Y
  isCurve := h_curve
  regular := h_regular
  projective := h_projective
  functionFieldIso := φ

/-- A regular projective curve is its own model, using the identity on its function field. -/
noncomputable def self {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [Scheme.Regular X.left] [Projective X.hom] : WithIso X where
  curve := X
  isCurve := inferInstance
  regular := inferInstance
  projective := inferInstance
  functionFieldIso := Iso.refl _

/-- The curve, regularity, and projectivity conditions carried by a model. -/
theorem spec {k : Type u} [Field k] {X : SchemeOverField k} [Curve X]
    (M : WithIso X) :
    Curve M.curve ∧ Scheme.Regular M.curve.left ∧ Projective M.curve.hom := sorry

/-- The chosen function-field isomorphism determines birationality over the ground field. -/
theorem birational {k : Type u} [Field k] {X : SchemeOverField k} [Curve X]
    (M : WithIso X) : Scheme.BirationalOver X.hom M.curve.hom := sorry

/-- The model and original curve have isomorphic nonempty open subschemes over the ground field. -/
theorem isomorphicOpen {k : Type u} [Field k] {X : SchemeOverField k} [Curve X]
    (M : WithIso X) :
    HasIsomorphicNonemptyOpenSubschemesOver
      (Spec (CommRingCat.of k)) X.left M.curve.left := sorry

end WithIso

end AlgebraicGeometry.NonsingularProjectiveModel
