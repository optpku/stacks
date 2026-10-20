module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Glued
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Construction
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# The universal algebra map of the glued relative spectrum

The affine component is the canonical ring-to-global-sections map of `Spec`,
transported through the actual local identification of the glued scheme.
Sheaf gluing on the affine basis extends those maps to the universal algebra map.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite RingedSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

/-- The specified universal ring maps on the affine basis of the base scheme. -/
def relativeSpectrumGluedBasisAlgebraMap (A : S.QcAlgebraUnder) :
    (inducedFunctor (fun U : S.affineOpens ↦ (U : S.Opens))).op ⋙ A.obj.right.obj ⟶
      (inducedFunctor (fun U : S.affineOpens ↦ (U : S.Opens))).op ⋙
        ((TopCat.Sheaf.pushforward CommRingCat.{u}
          (relativeSpectrumRealization A).toBase.toShHom.hom.base).obj
            (relativeSpectrumRealization A).Y.sheaf).obj where
  app U :=
    let V : S.affineOpens := U.unop
    (Scheme.ΓSpecIso (qcAlgebraSectionRing A V)).inv ≫
      (relativeSpectrumGluedLocalIso A V).hom.appTop ≫
        (Scheme.Opens.topIso
          ((relativeSpectrumNativeGluingData A).toBase ⁻¹ᵁ (V : S.Opens))).hom
  naturality := sorry

/-- Extend the actual affine universal maps by the target structure sheaf's gluing operation. -/
def relativeSpectrumGluedUniversalAlgebraMap (A : S.QcAlgebraUnder) :
    A.obj ⟶ Under.mk
      (Hom.commRingSheafPushforwardMap (relativeSpectrumRealization A).toBase.toShHom) :=
  Under.homMk
    ⟨TopCat.Sheaf.restrictHomEquivHom A.obj.right.obj
      ((TopCat.Sheaf.pushforward CommRingCat.{u}
        (relativeSpectrumRealization A).toBase.toShHom.hom.base).obj
          (relativeSpectrumRealization A).Y.sheaf)
      (by simpa only [Subtype.range_coe] using S.isBasis_affineOpens)
      (relativeSpectrumGluedBasisAlgebraMap A)⟩ sorry

/-- The global universal map computes on each affine open by its prescribed local Spec map. -/
theorem relativeSpectrumGluedUniversalAlgebraMap_app (A : S.QcAlgebraUnder)
    (U : S.affineOpens) :
    (InducedCategory.Hom.hom (relativeSpectrumGluedUniversalAlgebraMap A).right).app
        (op (U : S.Opens)) =
      (relativeSpectrumGluedBasisAlgebraMap A).app (op U) := sorry

/-- An explicit relative-spectrum model obtained from gluing, with its actual universal map. -/
def relativeSpectrumOver (A : S.QcAlgebraUnder) : RelativeSpectrumOver A where
  scheme := (relativeSpectrumRealization A).Y
  π := (relativeSpectrumRealization A).toBase
  universalMap := relativeSpectrumGluedUniversalAlgebraMap A

/-- The constructed universal point represents the relative-spectrum functor. -/
instance relativeSpectrumOver_isRelativeSpectrumOver (A : S.QcAlgebraUnder) :
    IsRelativeSpectrumOver (relativeSpectrumOver A) where
  isRepresentedBy := sorry
  realizes := relativeSpectrumRealization_realizes A

/-- The selected scheme is the colimit of the actual affine section spectra. -/
theorem relativeSpectrumOver_scheme (A : S.QcAlgebraUnder) :
    (relativeSpectrumOver A).scheme = (relativeSpectrumNativeGluingData A).glued := rfl

/-- The model retains the actual affine-glued universal algebra map. -/
theorem relativeSpectrumOver_universalMap (A : S.QcAlgebraUnder) :
    (relativeSpectrumOver A).universalMap = relativeSpectrumGluedUniversalAlgebraMap A := rfl

end AlgebraicGeometry.Scheme
