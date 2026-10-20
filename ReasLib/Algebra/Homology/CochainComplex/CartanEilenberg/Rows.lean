/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Functoriality
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Row computations for Cartan--Eilenberg resolutions

This file exposes evaluated resolution comparisons, distinguishes column terms from genuine row
homology objects, and supplies the canonical isomorphisms between them.
-/

open CategoryTheory Limits

noncomputable section

universe v u

namespace CochainComplex.CartanEilenbergResolution

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K : CochainComplex.Plus A}

/-- Evaluation of the column-resolution comparison at vertical degree `q`. -/
@[stacks 015H "evaluation of a Cartan-Eilenberg column comparison"]
noncomputable abbrev Column.resolutionEvalIso (I : CartanEilenbergResolution K) (p q : ℤ) :
    ((I.columnResolution p).cochainComplex).X q ≅ I.term p q :=
  (HomologicalComplex.eval A (ComplexShape.up ℤ) q).mapIso (Column.resolutionIso I p)

/-- Evaluation of the cycles-resolution comparison at vertical degree `q`. -/
@[stacks 015H "evaluation of a cycles-column comparison"]
noncomputable abbrev Cycles.resolutionEvalIso (I : CartanEilenbergResolution K) (p q : ℤ) :
    ((I.cyclesResolution p).cochainComplex).X q ≅ (I.cyclesColumn p).X q :=
  (HomologicalComplex.eval A (ComplexShape.up ℤ) q).mapIso (Cycles.resolutionIso I p)

/-- Evaluation of the image-resolution comparison at vertical degree `q`. -/
@[stacks 015H "evaluation of an image-column comparison"]
noncomputable abbrev Image.resolutionEvalIso (I : CartanEilenbergResolution K) (p q : ℤ) :
    ((I.imageResolution p).cochainComplex).X q ≅ (I.imageColumn p).X q :=
  (HomologicalComplex.eval A (ComplexShape.up ℤ) q).mapIso (Image.resolutionIso I p)

/-- Evaluation of the cohomology-resolution comparison at vertical degree `q`. -/
@[stacks 015H "evaluation of a homology-column comparison"]
noncomputable abbrev Homology.resolutionEvalIso (I : CartanEilenbergResolution K) (p q : ℤ) :
    ((I.homologyResolution p).cochainComplex).X q ≅ (I.homologyColumn p).X q :=
  (HomologicalComplex.eval A (ComplexShape.up ℤ) q).mapIso (Homology.resolutionIso I p)

namespace Row

/-- The cycles in horizontal degree `p` of the row in vertical degree `q`. -/
@[stacks 015H "row cycles term"]
abbrev cycles (I : CartanEilenbergResolution K) (q p : ℤ) : A :=
  (I.row q).cycles p

/-- The image of the horizontal differential starting in degree `p` in the row of vertical
degree `q`. -/
@[stacks 015H "row image term"]
abbrev image (I : CartanEilenbergResolution K) (q p : ℤ) : A :=
  CategoryTheory.Limits.image ((I.row q).d p (p + 1))

/-- The homology in horizontal degree `p` of the row in vertical degree `q`. -/
@[stacks 015H "row homology term"]
abbrev homology (I : CartanEilenbergResolution K) (q p : ℤ) : A :=
  (I.row q).homology p

end Row

/-- The chosen cycles resolution, evaluated in a row, identifies with the actual row cycles. -/
@[stacks 015H "cycles resolution to row comparison"]
noncomputable abbrev Cycles.resolutionToRow
    (I : CartanEilenbergResolution K) (q p : ℤ) :
    ((I.cyclesResolution p).cochainComplex).X q ≅ Row.cycles I q p :=
  Cycles.resolutionEvalIso I p q ≪≫ (I.bicomplex.rowCyclesIso p q).symm

/-- The chosen image resolution, evaluated in a row, identifies with the actual row image. -/
@[stacks 015H "image resolution to row comparison"]
noncomputable abbrev Image.resolutionToRow
    (I : CartanEilenbergResolution K) (q p : ℤ) :
    ((I.imageResolution p).cochainComplex).X q ≅ Row.image I q p :=
  Image.resolutionEvalIso I p q ≪≫ (I.bicomplex.rowImageIso p (p + 1) q).symm

/-- The chosen homology resolution, evaluated in a row, identifies with the actual row homology. -/
@[stacks 015H "homology resolution to row comparison"]
noncomputable abbrev Homology.resolutionToRow
    (I : CartanEilenbergResolution K) (q p : ℤ) :
    ((I.homologyResolution p).cochainComplex).X q ≅ Row.homology I q p :=
  Homology.resolutionEvalIso I p q ≪≫ (I.bicomplex.rowHomologyIso p q).symm

end CochainComplex.CartanEilenbergResolution
