module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Rows
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of row comparisons for Cartan--Eilenberg resolutions

The pointwise row comparisons in `CartanEilenberg.Rows` are components of the chosen
cycles, image, and homology resolutions.  This leaf gives the vertical maps and the
component/naturality API used when those comparisons are assembled into larger diagrams.
-/

@[expose] public section

open CategoryTheory ComplexShape HomologicalComplex₂

noncomputable section

universe v u

namespace CochainComplex.CartanEilenbergResolution

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K : CochainComplex.Plus A}

namespace Row

/-- The map on row cycles induced by a vertical differential of the Cartan--Eilenberg bicomplex. -/
@[stacks 015H "the vertical map on row cycles"]
abbrev cyclesMap (I : CartanEilenbergResolution K) (p q r : ℤ) :
    Row.cycles I q p ⟶ Row.cycles I r p :=
  HomologicalComplex.cyclesMap (I.bicomplex.flip.d q r) p

/-- The map on row differential images induced by a vertical differential. -/
@[stacks 015H "the vertical map on row images"]
abbrev imageMap (I : CartanEilenbergResolution K) (p q r : ℤ) :
    Row.image I q p ⟶ Row.image I r p :=
  HomologicalComplex.imageMap (I.bicomplex.flip.d q r) p (p + 1)

/-- The map on row homology induced by a vertical differential. -/
@[stacks 015H "the vertical map on row homology"]
abbrev homologyMap (I : CartanEilenbergResolution K) (p q r : ℤ) :
    Row.homology I q p ⟶ Row.homology I r p :=
  HomologicalComplex.homologyMap (I.bicomplex.flip.d q r) p

/-- Consecutive vertical row-cycle maps compose to zero. -/
@[stacks 015H "the differential relation for row cycles"]
theorem cyclesMap_comp (I : CartanEilenbergResolution K) (p q r s : ℤ) :
    Row.cyclesMap I p q r ≫ Row.cyclesMap I p r s = 0 := sorry

/-- Consecutive vertical row-image maps compose to zero. -/
@[stacks 015H "the differential relation for row images"]
theorem imageMap_comp (I : CartanEilenbergResolution K) (p q r s : ℤ) :
    Row.imageMap I p q r ≫ Row.imageMap I p r s = 0 := sorry

/-- Consecutive vertical row-homology maps compose to zero. -/
@[stacks 015H "the differential relation for row homology"]
theorem homologyMap_comp (I : CartanEilenbergResolution K) (p q r s : ℤ) :
    Row.homologyMap I p q r ≫ Row.homologyMap I p r s = 0 := sorry

end Row

namespace Cycles

/-- The chosen cycles-resolution comparison commutes with vertical differentials. -/
@[stacks 015J "naturality of the cycles-resolution comparison", reassoc]
theorem resolutionIso_hom_d (I : CartanEilenbergResolution K) (p q r : ℤ) :
    (Cycles.resolutionIso I p).hom.f q ≫ (I.cyclesColumn p).d q r =
      (I.cyclesResolution p).cochainComplex.d q r ≫ (Cycles.resolutionIso I p).hom.f r := sorry

/-- The inverse cycles-resolution comparison commutes with vertical differentials. -/
@[stacks 015J "inverse naturality of the cycles-resolution comparison", reassoc]
theorem resolutionIso_inv_d (I : CartanEilenbergResolution K) (p q r : ℤ) :
    (I.cyclesColumn p).d q r ≫ (Cycles.resolutionIso I p).inv.f r =
      (Cycles.resolutionIso I p).inv.f q ≫
        (I.cyclesResolution p).cochainComplex.d q r := sorry

/-- The pointwise cycles comparison is natural for a vertical differential. -/
@[stacks 015J "pointwise cycles comparison naturality", reassoc]
theorem resolutionToRow_hom_naturality
    (I : CartanEilenbergResolution K) (p q r : ℤ) :
    (Cycles.resolutionToRow I q p).hom ≫ Row.cyclesMap I p q r =
      (I.cyclesResolution p).cochainComplex.d q r ≫
        (Cycles.resolutionToRow I r p).hom := sorry

/-- The inverse pointwise cycles comparison is natural for a vertical differential. -/
@[stacks 015J "inverse pointwise cycles comparison naturality", reassoc]
theorem resolutionToRow_inv_naturality
    (I : CartanEilenbergResolution K) (p q r : ℤ) :
    Row.cyclesMap I p q r ≫ (Cycles.resolutionToRow I r p).inv =
      (Cycles.resolutionToRow I q p).inv ≫
        (I.cyclesResolution p).cochainComplex.d q r := sorry

/-- Conjugating the row-cycles map by the pointwise comparison recovers the differential of the
chosen cycles resolution. -/
@[stacks 015J "cycles-resolution differential from the row comparison", reassoc]
theorem resolutionToRow_source_d
    (I : CartanEilenbergResolution K) (p q r : ℤ) :
    (Cycles.resolutionToRow I q p).hom ≫ Row.cyclesMap I p q r ≫
        (Cycles.resolutionToRow I r p).inv =
      (I.cyclesResolution p).cochainComplex.d q r := sorry

/-- Conjugating the cycles-resolution differential by the inverse pointwise comparison recovers
the vertical map on row cycles. -/
@[stacks 015J "row-cycles map from the resolution comparison", reassoc]
theorem resolutionToRow_target_d
    (I : CartanEilenbergResolution K) (p q r : ℤ) :
    (Cycles.resolutionToRow I q p).inv ≫
        (I.cyclesResolution p).cochainComplex.d q r ≫
        (Cycles.resolutionToRow I r p).hom =
      Row.cyclesMap I p q r := sorry

/-- The forward pointwise cycles comparison is the evaluated resolution comparison followed by
the inverse row comparison. -/
@[simp, stacks 015J "computation of the pointwise cycles comparison"]
theorem resolutionToRow_hom (I : CartanEilenbergResolution K) (p q : ℤ) :
    (Cycles.resolutionToRow I q p).hom =
      (Cycles.resolutionEvalIso I p q).hom ≫ (I.bicomplex.rowCyclesIso p q).inv := rfl

/-- The inverse pointwise cycles comparison is computed by the inverse row comparison followed by
the inverse evaluated resolution comparison. -/
@[simp]
theorem resolutionToRow_inv (I : CartanEilenbergResolution K) (p q : ℤ) :
    (Cycles.resolutionToRow I q p).inv =
      (I.bicomplex.rowCyclesIso p q).hom ≫ (Cycles.resolutionEvalIso I p q).inv := rfl

end Cycles

namespace Image

/-- The chosen image-resolution comparison commutes with vertical differentials. -/
@[stacks 015J "naturality of the image-resolution comparison", reassoc]
theorem resolutionIso_hom_d (I : CartanEilenbergResolution K) (p q r : ℤ) :
    (Image.resolutionIso I p).hom.f q ≫ (I.imageColumn p).d q r =
      (I.imageResolution p).cochainComplex.d q r ≫ (Image.resolutionIso I p).hom.f r := sorry

/-- The inverse image-resolution comparison commutes with vertical differentials. -/
@[stacks 015J "inverse naturality of the image-resolution comparison", reassoc]
theorem resolutionIso_inv_d (I : CartanEilenbergResolution K) (p q r : ℤ) :
    (I.imageColumn p).d q r ≫ (Image.resolutionIso I p).inv.f r =
      (Image.resolutionIso I p).inv.f q ≫
        (I.imageResolution p).cochainComplex.d q r := sorry

/-- The pointwise image comparison is natural for a vertical differential. -/
@[stacks 015J "pointwise image comparison naturality", reassoc]
theorem resolutionToRow_hom_naturality
    (I : CartanEilenbergResolution K) (p q r : ℤ) :
    (Image.resolutionToRow I q p).hom ≫ Row.imageMap I p q r =
      (I.imageResolution p).cochainComplex.d q r ≫
        (Image.resolutionToRow I r p).hom := sorry

/-- The inverse pointwise image comparison is natural for a vertical differential. -/
@[stacks 015J "inverse pointwise image comparison naturality", reassoc]
theorem resolutionToRow_inv_naturality
    (I : CartanEilenbergResolution K) (p q r : ℤ) :
    Row.imageMap I p q r ≫ (Image.resolutionToRow I r p).inv =
      (Image.resolutionToRow I q p).inv ≫
        (I.imageResolution p).cochainComplex.d q r := sorry

/-- Conjugating the row-image map by the pointwise comparison recovers the differential of the
chosen image resolution. -/
@[stacks 015J "image-resolution differential from the row comparison", reassoc]
theorem resolutionToRow_source_d
    (I : CartanEilenbergResolution K) (p q r : ℤ) :
    (Image.resolutionToRow I q p).hom ≫ Row.imageMap I p q r ≫
        (Image.resolutionToRow I r p).inv =
      (I.imageResolution p).cochainComplex.d q r := sorry

/-- Conjugating the image-resolution differential by the inverse pointwise comparison recovers
the vertical map on row images. -/
@[stacks 015J "row-image map from the resolution comparison", reassoc]
theorem resolutionToRow_target_d
    (I : CartanEilenbergResolution K) (p q r : ℤ) :
    (Image.resolutionToRow I q p).inv ≫
        (I.imageResolution p).cochainComplex.d q r ≫
        (Image.resolutionToRow I r p).hom =
      Row.imageMap I p q r := sorry

/-- The forward pointwise image comparison is the evaluated resolution comparison followed by
the inverse row comparison. -/
@[simp, stacks 015J "computation of the pointwise image comparison"]
theorem resolutionToRow_hom (I : CartanEilenbergResolution K) (p q : ℤ) :
    (Image.resolutionToRow I q p).hom =
      (Image.resolutionEvalIso I p q).hom ≫
        (I.bicomplex.rowImageIso p (p + 1) q).inv := rfl

/-- The inverse pointwise image comparison is computed by the inverse row comparison followed by
the inverse evaluated resolution comparison. -/
@[simp]
theorem resolutionToRow_inv (I : CartanEilenbergResolution K) (p q : ℤ) :
    (Image.resolutionToRow I q p).inv =
      (I.bicomplex.rowImageIso p (p + 1) q).hom ≫
        (Image.resolutionEvalIso I p q).inv := rfl

end Image

namespace Homology

/-- The chosen homology-resolution comparison commutes with vertical differentials. -/
@[stacks 015J "naturality of the homology-resolution comparison", reassoc]
theorem resolutionIso_hom_d (I : CartanEilenbergResolution K) (p q r : ℤ) :
    (Homology.resolutionIso I p).hom.f q ≫ (I.homologyColumn p).d q r =
      (I.homologyResolution p).cochainComplex.d q r ≫
        (Homology.resolutionIso I p).hom.f r := sorry

/-- The inverse homology-resolution comparison commutes with vertical differentials. -/
@[stacks 015J "inverse naturality of the homology-resolution comparison", reassoc]
theorem resolutionIso_inv_d (I : CartanEilenbergResolution K) (p q r : ℤ) :
    (I.homologyColumn p).d q r ≫ (Homology.resolutionIso I p).inv.f r =
      (Homology.resolutionIso I p).inv.f q ≫
        (I.homologyResolution p).cochainComplex.d q r := sorry

/-- The pointwise homology comparison is natural for a vertical differential. -/
@[stacks 015J "pointwise homology comparison naturality", reassoc]
theorem resolutionToRow_hom_naturality
    (I : CartanEilenbergResolution K) (p q r : ℤ) :
    (Homology.resolutionToRow I q p).hom ≫ Row.homologyMap I p q r =
      (I.homologyResolution p).cochainComplex.d q r ≫
        (Homology.resolutionToRow I r p).hom := sorry

/-- The inverse pointwise homology comparison is natural for a vertical differential. -/
@[stacks 015J "inverse pointwise homology comparison naturality", reassoc]
theorem resolutionToRow_inv_naturality
    (I : CartanEilenbergResolution K) (p q r : ℤ) :
    Row.homologyMap I p q r ≫ (Homology.resolutionToRow I r p).inv =
      (Homology.resolutionToRow I q p).inv ≫
        (I.homologyResolution p).cochainComplex.d q r := sorry

/-- Conjugating the row-homology map by the pointwise comparison recovers the differential of the
chosen homology resolution. -/
@[stacks 015J "homology-resolution differential from the row comparison", reassoc]
theorem resolutionToRow_source_d
    (I : CartanEilenbergResolution K) (p q r : ℤ) :
    (Homology.resolutionToRow I q p).hom ≫ Row.homologyMap I p q r ≫
        (Homology.resolutionToRow I r p).inv =
      (I.homologyResolution p).cochainComplex.d q r := sorry

/-- Conjugating the homology-resolution differential by the inverse pointwise comparison recovers
the vertical map on row homology. -/
@[stacks 015J "row-homology map from the resolution comparison", reassoc]
theorem resolutionToRow_target_d
    (I : CartanEilenbergResolution K) (p q r : ℤ) :
    (Homology.resolutionToRow I q p).inv ≫
        (I.homologyResolution p).cochainComplex.d q r ≫
        (Homology.resolutionToRow I r p).hom =
      Row.homologyMap I p q r := sorry

/-- The forward pointwise homology comparison is the evaluated resolution comparison followed by
the inverse row comparison. -/
@[simp, stacks 015J "computation of the pointwise homology comparison"]
theorem resolutionToRow_hom (I : CartanEilenbergResolution K) (p q : ℤ) :
    (Homology.resolutionToRow I q p).hom =
      (Homology.resolutionEvalIso I p q).hom ≫
        (I.bicomplex.rowHomologyIso p q).inv := rfl

/-- The inverse pointwise homology comparison is computed by the inverse row comparison followed by
the inverse evaluated resolution comparison. -/
@[simp]
theorem resolutionToRow_inv (I : CartanEilenbergResolution K) (p q : ℤ) :
    (Homology.resolutionToRow I q p).inv =
      (I.bicomplex.rowHomologyIso p q).hom ≫
        (Homology.resolutionEvalIso I p q).inv := rfl

end Homology

end CochainComplex.CartanEilenbergResolution
