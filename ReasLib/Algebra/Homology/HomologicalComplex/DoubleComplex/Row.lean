/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.HomologicalComplex.Image
public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images

/-!
# Rowwise homology objects of a double complex

Evaluation at a row commutes canonically with cycles, differential images, and homology.  This
file packages those comparison isomorphisms and the maps induced by a morphism into a row of a
double complex.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u w₁ w₂

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  {I₁ : Type w₁} {I₂ : Type w₂} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}

/-- Cycles of a row are canonically the corresponding component of the cycles complex. -/
noncomputable def rowCyclesIso (D : HomologicalComplex₂ C c₁ c₂) (i : I₁) (q : I₂) :
    ((HomologicalComplex₂.flip D).X q).cycles i ≅ (D.cycles i).X q :=
  (D.sc i).mapCyclesIso (HomologicalComplex.eval C c₂ q)

/-- The image of a differential in a row is canonically the corresponding component of the
image complex. -/
noncomputable def rowImageIso (D : HomologicalComplex₂ C c₁ c₂) (i j : I₁) (q : I₂) :
    image (((HomologicalComplex₂.flip D).X q).d i j) ≅ (image (D.d i j)).X q :=
  image.eqToIso ((HomologicalComplex₂.flip_X_d D q i j).trans
      (HomologicalComplex.eval_map C c₂ q (D.d i j)).symm) ≪≫
    CategoryTheory.PreservesImage.iso
      (HomologicalComplex.eval C c₂ q) (D.d i j) ≪≫
    (eqToIso (HomologicalComplex.eval_obj C c₂ q (image (D.d i j))) :
      (HomologicalComplex.eval C c₂ q).obj (image (D.d i j)) ≅
        (image (D.d i j)).X q)

/-- Homology of a row is canonically the corresponding component of the homology complex. -/
noncomputable def rowHomologyIso (D : HomologicalComplex₂ C c₁ c₂) (i : I₁) (q : I₂) :
    ((HomologicalComplex₂.flip D).X q).homology i ≅ (D.homology i).X q :=
  (D.sc i).mapHomologyIso (HomologicalComplex.eval C c₂ q)

/-- The map on cycles induced by a morphism from a complex to a row of a double complex. -/
noncomputable def rowCyclesMap (D : HomologicalComplex₂ C c₁ c₂)
    {K : HomologicalComplex C c₁} {q : I₂}
    (φ : K ⟶ (HomologicalComplex₂.flip D).X q) (i : I₁) :
    K.cycles i ⟶ (D.cycles i).X q :=
  HomologicalComplex.cyclesMap φ i ≫ (D.rowCyclesIso i q).hom

/-- The map on differential images induced by a morphism from a complex to a row of a double
complex. -/
noncomputable def rowImageMap (D : HomologicalComplex₂ C c₁ c₂)
    {K : HomologicalComplex C c₁} {q : I₂}
    (φ : K ⟶ (HomologicalComplex₂.flip D).X q) (i j : I₁) :
    image (K.d i j) ⟶ (image (D.d i j)).X q :=
  HomologicalComplex.imageMap φ i j ≫ (D.rowImageIso i j q).hom

/-- The map on homology induced by a morphism from a complex to a row of a double complex. -/
noncomputable def rowHomologyMap (D : HomologicalComplex₂ C c₁ c₂)
    {K : HomologicalComplex C c₁} {q : I₂}
    (φ : K ⟶ (HomologicalComplex₂.flip D).X q) (i : I₁) :
    K.homology i ⟶ (D.homology i).X q :=
  HomologicalComplex.homologyMap φ i ≫ (D.rowHomologyIso i q).hom

/-- The rowwise cycles map is characterized by the inclusion into the corresponding term. -/
@[reassoc (attr := simp)]
theorem rowCyclesMap_iCycles (D : HomologicalComplex₂ C c₁ c₂)
    {K : HomologicalComplex C c₁} {q : I₂}
    (φ : K ⟶ (HomologicalComplex₂.flip D).X q) (i : I₁) :
    D.rowCyclesMap φ i ≫ (D.iCycles i).f q = K.iCycles i ≫ φ.f i := sorry

/-- Factoring a differential through its image commutes with the rowwise image map. -/
@[reassoc (attr := simp)]
theorem factorThruImage_rowImageMap (D : HomologicalComplex₂ C c₁ c₂)
    {K : HomologicalComplex C c₁} {q : I₂}
    (φ : K ⟶ (HomologicalComplex₂.flip D).X q) (i j : I₁) :
    factorThruImage (K.d i j) ≫ D.rowImageMap φ i j =
      φ.f i ≫ (factorThruImage (D.d i j)).f q := sorry

/-- The rowwise image map commutes with the inclusion of the image. -/
@[reassoc (attr := simp)]
theorem rowImageMap_image_ι (D : HomologicalComplex₂ C c₁ c₂)
    {K : HomologicalComplex C c₁} {q : I₂}
    (φ : K ⟶ (HomologicalComplex₂.flip D).X q) (i j : I₁) :
    D.rowImageMap φ i j ≫ (image.ι (D.d i j)).f q =
      image.ι (K.d i j) ≫ φ.f j := sorry

/-- Passing from cycles to homology commutes with the rowwise homology map. -/
@[reassoc (attr := simp)]
theorem homologyπ_rowHomologyMap (D : HomologicalComplex₂ C c₁ c₂)
    {K : HomologicalComplex C c₁} {q : I₂}
    (φ : K ⟶ (HomologicalComplex₂.flip D).X q) (i : I₁) :
    K.homologyπ i ≫ D.rowHomologyMap φ i =
      D.rowCyclesMap φ i ≫ (D.homologyπ i).f q := sorry

/-- A rowwise cycles map is uniquely determined by its composite with the cycles inclusion. -/
theorem rowCyclesMap_unique (D : HomologicalComplex₂ C c₁ c₂)
    {K : HomologicalComplex C c₁} {q : I₂}
    (φ : K ⟶ (HomologicalComplex₂.flip D).X q) (i : I₁)
    (g : K.cycles i ⟶ (D.cycles i).X q)
    (hg : g ≫ (D.iCycles i).f q = K.iCycles i ≫ φ.f i) :
    g = D.rowCyclesMap φ i := sorry

/-- A rowwise image map is uniquely determined by its composite with the image inclusion. -/
theorem rowImageMap_unique (D : HomologicalComplex₂ C c₁ c₂)
    {K : HomologicalComplex C c₁} {q : I₂}
    (φ : K ⟶ (HomologicalComplex₂.flip D).X q) (i j : I₁)
    (g : image (K.d i j) ⟶ (image (D.d i j)).X q)
    (hg : g ≫ (image.ι (D.d i j)).f q = image.ι (K.d i j) ≫ φ.f j) :
    g = D.rowImageMap φ i j := sorry

/-- A rowwise homology map is uniquely determined by its precomposition with the homology
projection. -/
theorem rowHomologyMap_unique (D : HomologicalComplex₂ C c₁ c₂)
    {K : HomologicalComplex C c₁} {q : I₂}
    (φ : K ⟶ (HomologicalComplex₂.flip D).X q) (i : I₁)
    (g : K.homology i ⟶ (D.homology i).X q)
    (hg : K.homologyπ i ≫ g = D.rowCyclesMap φ i ≫ (D.homologyπ i).f q) :
    g = D.rowHomologyMap φ i := sorry

/-- Rowwise cycles maps are natural under precomposition of the source complex. -/
@[reassoc (attr := simp)]
theorem rowCyclesMap_comp (D : HomologicalComplex₂ C c₁ c₂)
    {K L : HomologicalComplex C c₁} {q : I₂}
    (ψ : K ⟶ L) (φ : L ⟶ (HomologicalComplex₂.flip D).X q) (i : I₁) :
    D.rowCyclesMap (ψ ≫ φ) i =
      HomologicalComplex.cyclesMap ψ i ≫ D.rowCyclesMap φ i := sorry

/-- Rowwise image maps are natural under precomposition of the source complex. -/
@[reassoc (attr := simp)]
theorem rowImageMap_comp (D : HomologicalComplex₂ C c₁ c₂)
    {K L : HomologicalComplex C c₁} {q : I₂}
    (ψ : K ⟶ L) (φ : L ⟶ (HomologicalComplex₂.flip D).X q) (i j : I₁) :
    D.rowImageMap (ψ ≫ φ) i j =
      HomologicalComplex.imageMap ψ i j ≫ D.rowImageMap φ i j := sorry

/-- Rowwise homology maps are natural under precomposition of the source complex. -/
@[reassoc (attr := simp)]
theorem rowHomologyMap_comp (D : HomologicalComplex₂ C c₁ c₂)
    {K L : HomologicalComplex C c₁} {q : I₂}
    (ψ : K ⟶ L) (φ : L ⟶ (HomologicalComplex₂.flip D).X q) (i : I₁) :
    D.rowHomologyMap (ψ ≫ φ) i =
      HomologicalComplex.homologyMap ψ i ≫ D.rowHomologyMap φ i := sorry

/-- The row-homology comparison commutes with the differential in the other direction. -/
@[reassoc]
theorem rowHomologyIso_hom_d
    (D : HomologicalComplex₂ C c₁ c₂) (i : I₁) (q r : I₂)
    (hqr : c₂.Rel q r) :
    (D.rowHomologyIso i q).hom ≫ (D.homology i).d q r =
      HomologicalComplex.homologyMap (D.flip.d q r) i ≫
        (D.rowHomologyIso i r).hom := sorry

/-- Taking row homology and then varying the row is canonically the homology complex in the
first direction of the original double complex. -/
noncomputable def rowHomologyComplexIso
    (D : HomologicalComplex₂ C c₁ c₂) (i : I₁) :
    ((HomologicalComplex.homologyFunctor C c₁ i).mapHomologicalComplex c₂).obj D.flip ≅
      D.homology i :=
  HomologicalComplex.Hom.isoOfComponents
    (D.rowHomologyIso i) (D.rowHomologyIso_hom_d i)

/-- The row-homology complex comparison evaluates to `rowHomologyIso`. -/
@[simp]
theorem rowHomologyComplexIso_hom_f
    (D : HomologicalComplex₂ C c₁ c₂) (i : I₁) (q : I₂) :
    (D.rowHomologyComplexIso i).hom.f q = (D.rowHomologyIso i q).hom := sorry

end HomologicalComplex
