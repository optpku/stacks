/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Views.Rows

/-!
# Canonical naturality for views of Cartan--Eilenberg resolution maps

The cycles, image, and homology views commute with their canonical inclusions and projections.
The rowwise views also agree with evaluating the corresponding columnwise complexes through the
standard row comparison isomorphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape HomologicalComplex₂

noncomputable section

universe v u

namespace CochainComplex.CartanEilenbergResolution.Map

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K L : CochainComplex.Plus A}
variable {I : CartanEilenbergResolution K} {J : CartanEilenbergResolution L}

/-- A cycles-column map commutes with the canonical cycles inclusion. -/
@[reassoc (attr := simp), stacks 015J "naturality of a Cartan-Eilenberg cycles-column map"]
theorem cyclesColumn_iCycles (f : Map I J) (p : ℤ) :
    cyclesColumn f p ≫ J.bicomplex.iCycles p =
      I.bicomplex.iCycles p ≫ column f p := sorry

/-- An image-column map commutes with the canonical image inclusion. -/
@[reassoc (attr := simp), stacks 015J "naturality of a Cartan-Eilenberg image-column map"]
theorem imageColumn_image_ι (f : Map I J) (p : ℤ) :
    imageColumn f p ≫ image.ι (J.bicomplex.d p (p + 1)) =
      image.ι (I.bicomplex.d p (p + 1)) ≫ column f (p + 1) := sorry

/-- A homology-column map commutes with the canonical projection from cycles. -/
@[reassoc (attr := simp), stacks 015J "naturality of a Cartan-Eilenberg homology-column map"]
theorem homologyColumn_homologyπ (f : Map I J) (p : ℤ) :
    I.bicomplex.homologyπ p ≫ homologyColumn f p =
      cyclesColumn f p ≫ J.bicomplex.homologyπ p := sorry

/-- A row-cycles map commutes with the canonical cycles inclusion. -/
@[reassoc (attr := simp), stacks 015J "naturality of a Cartan-Eilenberg row-cycles map"]
theorem cyclesRow_iCycles (f : Map I J) (q p : ℤ) :
    cyclesRow f q p ≫ (J.row q).iCycles p =
      (I.row q).iCycles p ≫ term f p q := sorry

/-- A row-image map commutes with the canonical image inclusion. -/
@[reassoc (attr := simp), stacks 015J "naturality of a Cartan-Eilenberg row-image map"]
theorem imageRow_image_ι (f : Map I J) (q p : ℤ) :
    imageRow f q p ≫ image.ι ((J.row q).d p (p + 1)) =
      image.ι ((I.row q).d p (p + 1)) ≫ term f (p + 1) q := sorry

/-- A row-homology map commutes with the canonical projection from row cycles. -/
@[reassoc (attr := simp), stacks 015J "naturality of a Cartan-Eilenberg row-homology map"]
theorem homologyRow_homologyπ (f : Map I J) (q p : ℤ) :
    (I.row q).homologyπ p ≫ homologyRow f q p =
      cyclesRow f q p ≫ (J.row q).homologyπ p := sorry

/-- The row-cycles map agrees with the evaluated cycles-column map under the row comparison. -/
@[reassoc, stacks 015J "row-column compatibility of Cartan-Eilenberg cycles maps"]
theorem cyclesRow_comparison (f : Map I J) (q p : ℤ) :
    cyclesRow f q p ≫ (J.bicomplex.rowCyclesIso p q).hom =
      (I.bicomplex.rowCyclesIso p q).hom ≫ (cyclesColumn f p).f q := sorry

/-- Inverse naturality of the row-cycles comparison. -/
@[reassoc, stacks 015J "inverse row-column compatibility of Cartan-Eilenberg cycles maps"]
theorem cyclesRow_comparison_inv_naturality (f : Map I J) (q p : ℤ) :
    (cyclesColumn f p).f q ≫ (J.bicomplex.rowCyclesIso p q).inv =
      (I.bicomplex.rowCyclesIso p q).inv ≫ cyclesRow f q p := sorry

/-- Conjugating the evaluated cycles-column map by the row comparison recovers the row-cycles map.
-/
@[reassoc, stacks 015J "computation of Cartan-Eilenberg row-cycles maps"]
theorem cyclesRow_comparison_naturality_inv (f : Map I J) (q p : ℤ) :
    (I.bicomplex.rowCyclesIso p q).hom ≫ (cyclesColumn f p).f q ≫
        (J.bicomplex.rowCyclesIso p q).inv =
      cyclesRow f q p := sorry

/-- Conjugating the row-cycles map by the inverse row comparison recovers the evaluated
cycles-column map. -/
@[reassoc, stacks 015J "target-map computation of Cartan-Eilenberg row-cycles maps"]
theorem cyclesRow_comparison_target_map (f : Map I J) (q p : ℤ) :
    (I.bicomplex.rowCyclesIso p q).inv ≫ cyclesRow f q p ≫
        (J.bicomplex.rowCyclesIso p q).hom =
      (cyclesColumn f p).f q := sorry

/-- The row-image map agrees with the evaluated image-column map under the row comparison. -/
@[reassoc, stacks 015J "row-column compatibility of Cartan-Eilenberg image maps"]
theorem imageRow_comparison (f : Map I J) (q p : ℤ) :
    imageRow f q p ≫ (J.bicomplex.rowImageIso p (p + 1) q).hom =
      (I.bicomplex.rowImageIso p (p + 1) q).hom ≫ (imageColumn f p).f q := sorry

/-- Inverse naturality of the row-image comparison. -/
@[reassoc, stacks 015J "inverse row-column compatibility of Cartan-Eilenberg image maps"]
theorem imageRow_comparison_inv_naturality (f : Map I J) (q p : ℤ) :
    (imageColumn f p).f q ≫ (J.bicomplex.rowImageIso p (p + 1) q).inv =
      (I.bicomplex.rowImageIso p (p + 1) q).inv ≫ imageRow f q p := sorry

/-- Conjugating the evaluated image-column map by the row comparison recovers the row-image map. -/
@[reassoc, stacks 015J "computation of Cartan-Eilenberg row-image maps"]
theorem imageRow_comparison_naturality_inv (f : Map I J) (q p : ℤ) :
    (I.bicomplex.rowImageIso p (p + 1) q).hom ≫ (imageColumn f p).f q ≫
        (J.bicomplex.rowImageIso p (p + 1) q).inv =
      imageRow f q p := sorry

/-- Conjugating the row-image map by the inverse row comparison recovers the evaluated
image-column map. -/
@[reassoc, stacks 015J "target-map computation of Cartan-Eilenberg row-image maps"]
theorem imageRow_comparison_target_map (f : Map I J) (q p : ℤ) :
    (I.bicomplex.rowImageIso p (p + 1) q).inv ≫ imageRow f q p ≫
        (J.bicomplex.rowImageIso p (p + 1) q).hom =
      (imageColumn f p).f q := sorry

/-- The row-homology map agrees with the evaluated homology-column map under the row comparison. -/
@[reassoc, stacks 015J "row-column compatibility of Cartan-Eilenberg homology maps"]
theorem homologyRow_comparison (f : Map I J) (q p : ℤ) :
    homologyRow f q p ≫ (J.bicomplex.rowHomologyIso p q).hom =
      (I.bicomplex.rowHomologyIso p q).hom ≫ (homologyColumn f p).f q := sorry

/-- Inverse naturality of the row-homology comparison. -/
@[reassoc, stacks 015J "inverse row-column compatibility of Cartan-Eilenberg homology maps"]
theorem homologyRow_comparison_inv_naturality (f : Map I J) (q p : ℤ) :
    (homologyColumn f p).f q ≫ (J.bicomplex.rowHomologyIso p q).inv =
      (I.bicomplex.rowHomologyIso p q).inv ≫ homologyRow f q p := sorry

/-- Conjugating the evaluated homology-column map by the row comparison recovers the row-homology
map. -/
@[reassoc, stacks 015J "computation of Cartan-Eilenberg row-homology maps"]
theorem homologyRow_comparison_naturality_inv (f : Map I J) (q p : ℤ) :
    (I.bicomplex.rowHomologyIso p q).hom ≫ (homologyColumn f p).f q ≫
        (J.bicomplex.rowHomologyIso p q).inv =
      homologyRow f q p := sorry

/-- Conjugating the row-homology map by the inverse row comparison recovers the evaluated
homology-column map. -/
@[reassoc, stacks 015J "target-map computation of Cartan-Eilenberg row-homology maps"]
theorem homologyRow_comparison_target_map (f : Map I J) (q p : ℤ) :
    (I.bicomplex.rowHomologyIso p q).inv ≫ homologyRow f q p ≫
        (J.bicomplex.rowHomologyIso p q).hom =
      (homologyColumn f p).f q := sorry

end CochainComplex.CartanEilenbergResolution.Map
