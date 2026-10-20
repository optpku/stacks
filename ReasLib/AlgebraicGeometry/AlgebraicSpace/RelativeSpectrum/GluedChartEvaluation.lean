module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.ChartEvaluationCover

/-!
# Evaluate algebra sections on the concrete chart spectrum

Both scheme charts may be nonaffine. Restrict a morphism into the constructed
chart spectrum to the inverse images of the target's affine opens, use the
actual local spectrum identifications and affine scalar-extension evaluation,
then amalgamate the resulting ring maps on the test scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {E : Scheme.{u}}

/-- Restrict the map into the constructed spectrum to its actual affine section spectrum. -/
def relativeSpectrumGluedPointAffineMap (A : X.QcAlgebraUnder) (V : smallEtaleSite X)
    (e : E ⟶ (Scheme.relativeSpectrumOver (onChart A V)).scheme) (P : V.left.left.affineOpens) :
    (((e ≫ (Scheme.relativeSpectrumOver (onChart A V)).π) ⁻¹ᵁ
      (P : V.left.left.Opens))).toScheme ⟶
        Spec (sectionRing A ((chartOpens V).obj (P : V.left.left.Opens))) :=
  e.resLE
      ((Scheme.relativeSpectrumOver (onChart A V)).π ⁻¹ᵁ (P : V.left.left.Opens))
      ((e ≫ (Scheme.relativeSpectrumOver (onChart A V)).π) ⁻¹ᵁ (P : V.left.left.Opens)) sorry ≫
    (Scheme.relativeSpectrumGluedLocalIso (onChart A V) P).hom

/-- The geometric triangle places the pulled-back target open inside the source-map preimage. -/
theorem relativeSpectrumGluedPointSourceMap_open_le (A : X.QcAlgebraUnder)
    {R V : smallEtaleSite X} (m : R ⟶ V) (f : E ⟶ R.left.left)
    (e : E ⟶ (Scheme.relativeSpectrumOver (onChart A V)).scheme)
    (h : e ≫ (Scheme.relativeSpectrumOver (onChart A V)).π = f ≫ m.left.left)
    (P : V.left.left.affineOpens) :
    (e ≫ (Scheme.relativeSpectrumOver (onChart A V)).π) ⁻¹ᵁ (P : V.left.left.Opens) ≤
      f ⁻¹ᵁ (m.left.left ⁻¹ᵁ (P : V.left.left.Opens)) := sorry

/-- The source-chart map restricted to the open over an affine target open. -/
def relativeSpectrumGluedPointSourceMap (A : X.QcAlgebraUnder) {R V : smallEtaleSite X}
    (m : R ⟶ V) (f : E ⟶ R.left.left)
    (e : E ⟶ (Scheme.relativeSpectrumOver (onChart A V)).scheme)
    (h : e ≫ (Scheme.relativeSpectrumOver (onChart A V)).π = f ≫ m.left.left)
    (P : V.left.left.affineOpens) :
    (((e ≫ (Scheme.relativeSpectrumOver (onChart A V)).π) ⁻¹ᵁ
      (P : V.left.left.Opens))).toScheme ⟶ (m.left.left ⁻¹ᵁ (P : V.left.left.Opens)).toScheme :=
  f.resLE (m.left.left ⁻¹ᵁ (P : V.left.left.Opens))
    ((e ≫ (Scheme.relativeSpectrumOver (onChart A V)).π) ⁻¹ᵁ (P : V.left.left.Opens))
    (relativeSpectrumGluedPointSourceMap_open_le A m f e h P)

/-- The actual restricted point maps satisfy the scalar triangle on each affine target open. -/
theorem relativeSpectrumGluedPointAffineTriangle (A : X.QcAlgebraUnder)
    {R V : smallEtaleSite X} (m : R ⟶ V) (f : E ⟶ R.left.left)
    (e : E ⟶ (Scheme.relativeSpectrumOver (onChart A V)).scheme)
    (h : e ≫ (Scheme.relativeSpectrumOver (onChart A V)).π = f ≫ m.left.left)
    (P : V.left.left.affineOpens) :
    relativeSpectrumGluedPointAffineMap A V e P ≫
        Spec.map (structureMap A ((chartOpens V).obj (P : V.left.left.Opens))) =
      relativeSpectrumGluedPointSourceMap A m f e h P ≫
        (chartOpenRestrictionMap m (P : V.left.left.Opens)).left.left ≫
          (((chartOpens V).obj (P : V.left.left.Opens)).left.left).toSpecΓ := sorry

/-- The original source sections are evaluated on one pulled-back affine target open. -/
def relativeSpectrumGluedPointEvaluationOnAffineOpen (A : X.QcAlgebraUnder)
    {R V : smallEtaleSite X} (m : R ⟶ V) (f : E ⟶ R.left.left)
    (e : E ⟶ (Scheme.relativeSpectrumOver (onChart A V)).scheme)
    (h : e ≫ (Scheme.relativeSpectrumOver (onChart A V)).π = f ≫ m.left.left)
    (P : V.left.left.affineOpens) :
    sectionRing A R ⟶ E.presheaf.obj (op
      ((e ≫ (Scheme.relativeSpectrumOver (onChart A V)).π) ⁻¹ᵁ (P : V.left.left.Opens))) := by
  -- Local instance justification (defeq pin): the target open chart's scheme is the affine P.
  letI : IsAffine ((chartOpens V).obj (P : V.left.left.Opens)).left.left :=
    inferInstanceAs (IsAffine (P : V.left.left.Opens).toScheme)
  exact A.obj.right.obj.map
      (relativeSpectrumOpenChartInclusion R (m.left.left ⁻¹ᵁ (P : V.left.left.Opens))).op ≫
    relativeSpectrumPointEvaluation A (chartOpenRestrictionMap m (P : V.left.left.Opens))
      (relativeSpectrumGluedPointSourceMap A m f e h P)
      (relativeSpectrumGluedPointAffineMap A V e P)
      (relativeSpectrumGluedPointAffineTriangle A m f e h P) ≫
    (Scheme.Opens.topIso
      ((e ≫ (Scheme.relativeSpectrumOver (onChart A V)).π) ⁻¹ᵁ (P : V.left.left.Opens))).hom

/-- Local evaluation maps agree on every common open of the test scheme. -/
theorem relativeSpectrumGluedPointEvaluationOnAffineOpen_compatible (A : X.QcAlgebraUnder)
    {R V : smallEtaleSite X} (m : R ⟶ V) (f : E ⟶ R.left.left)
    (e : E ⟶ (Scheme.relativeSpectrumOver (onChart A V)).scheme)
    (h : e ≫ (Scheme.relativeSpectrumOver (onChart A V)).π = f ≫ m.left.left)
    {W : E.Opens} {P P' : V.left.left.affineOpens}
    (a : W ⟶ (e ≫ (Scheme.relativeSpectrumOver (onChart A V)).π) ⁻¹ᵁ (P : V.left.left.Opens))
    (b : W ⟶ (e ≫ (Scheme.relativeSpectrumOver (onChart A V)).π) ⁻¹ᵁ (P' : V.left.left.Opens)) :
    relativeSpectrumGluedPointEvaluationOnAffineOpen A m f e h P ≫ E.presheaf.map a.op =
      relativeSpectrumGluedPointEvaluationOnAffineOpen A m f e h P' ≫ E.presheaf.map b.op := sorry

/-- Evaluate the algebra on any source chart using the actual map into a constructed chart spectrum. -/
def relativeSpectrumGluedPointEvaluation (A : X.QcAlgebraUnder)
    {R V : smallEtaleSite X} (m : R ⟶ V) (f : E ⟶ R.left.left)
    (e : E ⟶ (Scheme.relativeSpectrumOver (onChart A V)).scheme)
    (h : e ≫ (Scheme.relativeSpectrumOver (onChart A V)).π = f ≫ m.left.left) :
    sectionRing A R ⟶ Γ(E, ⊤) :=
  E.sheaf.property.amalgamateOfArrows (fun _ ↦ homOfLE le_top)
    (relativeSpectrumPointEvaluation_affineCover_mem
      (R := V) (e ≫ (Scheme.relativeSpectrumOver (onChart A V)).π))
    (relativeSpectrumGluedPointEvaluationOnAffineOpen A m f e h)
    (by
      intro W P P' a b hab
      exact relativeSpectrumGluedPointEvaluationOnAffineOpen_compatible A m f e h a b)

end AlgebraicGeometry.AlgebraicSpace
