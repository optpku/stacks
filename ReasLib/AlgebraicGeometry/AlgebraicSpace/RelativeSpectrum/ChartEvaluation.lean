module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Algebra.ChartBaseChange

/-!
# Relative-spectrum evaluation after affine chart base change

A point of the actual section spectrum supplies its coefficient evaluation.
Its structural triangle supplies the scalar evaluation on an affine source
chart. The specified ring pushout and its canonical fiber inverse then give
the section map on that source chart.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {E : Scheme.{u}}

/-- Evaluate the affine algebra spectrum on the supplied actual scheme morphism. -/
def relativeSpectrumAffinePointEvaluation (A : X.QcAlgebraUnder) (V : smallEtaleSite X)
    (e : E ⟶ Spec (sectionRing A V)) : sectionRing A V ⟶ Γ(E, ⊤) :=
  (Scheme.ΓSpecIso (sectionRing A V)).inv ≫ e.appTop

/-- The geometric triangle gives the equality of the two scalar maps into the test scheme. -/
theorem relativeSpectrumAffinePointEvaluation_scalar (A : X.QcAlgebraUnder)
    {U V : smallEtaleSite X} (m : U ⟶ V) (f : E ⟶ U.left.left)
    (e : E ⟶ Spec (sectionRing A V))
    (h : e ≫ Spec.map (structureMap A V) = f ≫ m.left.left ≫ V.left.left.toSpecΓ) :
    structureMap A V ≫ relativeSpectrumAffinePointEvaluation A V e =
      m.left.left.appTop ≫ f.appTop := sorry

/-- Evaluate scalar-extended sections by the actual coefficient and scalar ring maps. -/
def relativeSpectrumAffinePointPushoutEvaluation (A : X.QcAlgebraUnder)
    {U V : smallEtaleSite X} (m : U ⟶ V) (f : E ⟶ U.left.left)
    (e : E ⟶ Spec (sectionRing A V))
    (h : e ≫ Spec.map (structureMap A V) = f ≫ m.left.left ≫ V.left.left.toSpecΓ) :
    sectionBaseChangeRing A m ⟶ Γ(E, ⊤) :=
  pushout.desc (relativeSpectrumAffinePointEvaluation A V e) f.appTop
    (relativeSpectrumAffinePointEvaluation_scalar A m f e h)

/-- The original source-chart algebra is evaluated by its specified affine scalar-extension inverse. -/
def relativeSpectrumAffinePointBaseChangeEvaluation (A : X.QcAlgebraUnder)
    {U V : smallEtaleSite X} [IsAffine U.left.left] [IsAffine V.left.left]
    (m : U ⟶ V) (f : E ⟶ U.left.left) (e : E ⟶ Spec (sectionRing A V))
    (h : e ≫ Spec.map (structureMap A V) = f ≫ m.left.left ≫ V.left.left.toSpecΓ) :
    sectionRing A U ⟶ Γ(E, ⊤) :=
  sectionBaseChangeInverse A m ≫ relativeSpectrumAffinePointPushoutEvaluation A m f e h

/-- Restricting coefficients from the target chart then evaluating recovers the supplied point. -/
theorem relativeSpectrumAffinePointBaseChangeEvaluation_restrict (A : X.QcAlgebraUnder)
    {U V : smallEtaleSite X} [IsAffine U.left.left] [IsAffine V.left.left]
    (m : U ⟶ V) (f : E ⟶ U.left.left) (e : E ⟶ Spec (sectionRing A V))
    (h : e ≫ Spec.map (structureMap A V) = f ≫ m.left.left ≫ V.left.left.toSpecΓ) :
    A.obj.right.obj.map m.op ≫ relativeSpectrumAffinePointBaseChangeEvaluation A m f e h =
      relativeSpectrumAffinePointEvaluation A V e := sorry

/-- The source-chart structure map is evaluated by the specified structural scheme morphism. -/
theorem relativeSpectrumAffinePointBaseChangeEvaluation_structure (A : X.QcAlgebraUnder)
    {U V : smallEtaleSite X} [IsAffine U.left.left] [IsAffine V.left.left]
    (m : U ⟶ V) (f : E ⟶ U.left.left) (e : E ⟶ Spec (sectionRing A V))
    (h : e ≫ Spec.map (structureMap A V) = f ≫ m.left.left ≫ V.left.left.toSpecΓ) :
    structureMap A U ≫ relativeSpectrumAffinePointBaseChangeEvaluation A m f e h =
      f.appTop := sorry

end AlgebraicGeometry.AlgebraicSpace
