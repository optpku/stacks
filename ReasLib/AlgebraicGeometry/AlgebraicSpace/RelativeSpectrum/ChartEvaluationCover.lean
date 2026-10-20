/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.ChartEvaluation
public import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Extend relative-spectrum point evaluation across affine chart covers

The source chart may be nonaffine. Pull its native affine-open covering back
to the test scheme, evaluate each actual affine chart by scalar extension,
then use the test scheme's structure sheaf to amalgamate the ring maps.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {E : Scheme.{u}}

/-- The actual open-immersion arrow from an open chart to its containing étale chart. -/
def relativeSpectrumOpenChartInclusion (U : smallEtaleSite X) (W : U.left.left.Opens) :
    (chartOpens U).obj W ⟶ U :=
  MorphismProperty.CostructuredArrow.homMk (Over.homMk W.ι rfl) trivial sorry

/-- Restrict the geometric point triangle to one affine open of its source chart. -/
theorem relativeSpectrumAffinePointEvaluation_restrictedTriangle (A : X.QcAlgebraUnder)
    {R V : smallEtaleSite X} (m : R ⟶ V) (f : E ⟶ R.left.left)
    (e : E ⟶ Spec (sectionRing A V))
    (h : e ≫ Spec.map (structureMap A V) = f ≫ m.left.left ≫ V.left.left.toSpecΓ)
    (Q : R.left.left.affineOpens) :
    ((f ⁻¹ᵁ (Q : R.left.left.Opens)).ι ≫ e) ≫ Spec.map (structureMap A V) =
      (f ∣_ (Q : R.left.left.Opens)) ≫
        ((relativeSpectrumOpenChartInclusion R Q) ≫ m).left.left ≫ V.left.left.toSpecΓ := sorry

/-- The ring map on a pulled-back affine source open, retaining the original chart restrictions. -/
def relativeSpectrumPointEvaluationOnAffineOpen (A : X.QcAlgebraUnder)
    {R V : smallEtaleSite X} [IsAffine V.left.left] (m : R ⟶ V)
    (f : E ⟶ R.left.left) (e : E ⟶ Spec (sectionRing A V))
    (h : e ≫ Spec.map (structureMap A V) = f ≫ m.left.left ≫ V.left.left.toSpecΓ)
    (Q : R.left.left.affineOpens) :
    sectionRing A R ⟶ E.presheaf.obj (op (f ⁻¹ᵁ (Q : R.left.left.Opens))) := by
  -- Local instance justification (defeq pin): the native open chart's underlying scheme is Q.
  letI : IsAffine ((chartOpens R).obj (Q : R.left.left.Opens)).left.left :=
    inferInstanceAs (IsAffine (Q : R.left.left.Opens).toScheme)
  exact A.obj.right.obj.map (relativeSpectrumOpenChartInclusion R Q).op ≫
    relativeSpectrumAffinePointBaseChangeEvaluation A
      ((relativeSpectrumOpenChartInclusion R Q) ≫ m)
      (f ∣_ (Q : R.left.left.Opens)) ((f ⁻¹ᵁ (Q : R.left.left.Opens)).ι ≫ e)
      (relativeSpectrumAffinePointEvaluation_restrictedTriangle A m f e h Q) ≫
    (Scheme.Opens.topIso (f ⁻¹ᵁ (Q : R.left.left.Opens))).hom

/-- The inverse images of the source chart's affine opens cover the test scheme. -/
theorem relativeSpectrumPointEvaluation_affineCover_mem {R : smallEtaleSite X}
    (f : E ⟶ R.left.left) :
    Sieve.ofArrows (fun Q : R.left.left.affineOpens ↦ f ⁻¹ᵁ (Q : R.left.left.Opens))
      (fun _ ↦ homOfLE le_top) ∈ (Opens.grothendieckTopology E) ⊤ := sorry

/-- The specified affine ring maps agree after every overlap restriction. -/
theorem relativeSpectrumPointEvaluationOnAffineOpen_compatible (A : X.QcAlgebraUnder)
    {R V : smallEtaleSite X} [IsAffine V.left.left] (m : R ⟶ V)
    (f : E ⟶ R.left.left) (e : E ⟶ Spec (sectionRing A V))
    (h : e ≫ Spec.map (structureMap A V) = f ≫ m.left.left ≫ V.left.left.toSpecΓ)
    {W : E.Opens} {Q Q' : R.left.left.affineOpens}
    (a : W ⟶ f ⁻¹ᵁ (Q : R.left.left.Opens))
    (b : W ⟶ f ⁻¹ᵁ (Q' : R.left.left.Opens)) :
    relativeSpectrumPointEvaluationOnAffineOpen A m f e h Q ≫ E.presheaf.map a.op =
      relativeSpectrumPointEvaluationOnAffineOpen A m f e h Q' ≫ E.presheaf.map b.op := sorry

/-- The actual point evaluation on any étale source chart, glued from its affine scalar extensions. -/
def relativeSpectrumPointEvaluation (A : X.QcAlgebraUnder)
    {R V : smallEtaleSite X} [IsAffine V.left.left] (m : R ⟶ V)
    (f : E ⟶ R.left.left) (e : E ⟶ Spec (sectionRing A V))
    (h : e ≫ Spec.map (structureMap A V) = f ≫ m.left.left ≫ V.left.left.toSpecΓ) :
    sectionRing A R ⟶ Γ(E, ⊤) :=
  E.sheaf.property.amalgamateOfArrows (fun _ ↦ homOfLE le_top)
    (relativeSpectrumPointEvaluation_affineCover_mem f)
    (relativeSpectrumPointEvaluationOnAffineOpen A m f e h)
    (by
      intro W Q Q' a b hab
      exact relativeSpectrumPointEvaluationOnAffineOpen_compatible A m f e h a b)

/-- On each pulled-back affine open the glued point evaluation has the specified ring map. -/
theorem relativeSpectrumPointEvaluation_affineOpen (A : X.QcAlgebraUnder)
    {R V : smallEtaleSite X} [IsAffine V.left.left] (m : R ⟶ V)
    (f : E ⟶ R.left.left) (e : E ⟶ Spec (sectionRing A V))
    (h : e ≫ Spec.map (structureMap A V) = f ≫ m.left.left ≫ V.left.left.toSpecΓ)
    (Q : R.left.left.affineOpens) :
    relativeSpectrumPointEvaluation A m f e h ≫ E.presheaf.map (homOfLE le_top).op =
      relativeSpectrumPointEvaluationOnAffineOpen A m f e h Q := sorry

end AlgebraicGeometry.AlgebraicSpace
