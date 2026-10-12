/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import ReasLib.CategoryTheory.Sites.Presheaf.InverseImage
public import stacks_project.Chap96.Lemma_96_18_1_CoveringSimplex
public import stacks_project.Chap96.Lemma_96_3_2_Comparison
public import stacks_project.Chap96.Lemma_96_3_3_Pullback

/-!
# The relative Čech complex of a 1-morphism of categories fibred in groupoids

The complex `K^•(f, F)` of abelian presheaves on `X` with terms
`f_{n,*} f_n⁻¹ F`, obtained from covering simplices by right Kan extension
along the apex functors and the Dold–Kan functor on the resulting
cosimplicial object.
-/

@[expose] public section

open CategoryTheory AlgebraicTopology Functor
open scoped Bicategory Simplicial

noncomputable section

universe u v w vS wA

namespace CategoryTheory.FiberedCategoryOver.Groupoids.RelativeCech

open Cech

variable {C : Type u} [Category.{v} C]
variable {U X : FiberedCategoryOver.Groupoids C}

/-- Pushforward comparison `(h ≫ f)_* ≅ h_* ⋙ f_*` of abelian-group-valued
presheaves, the conjugate of `presheafInverseImage_compIso` followed by
`Functor.ranCompIso`. -/
def pushforwardCompIso {V : FiberedCategoryOver.Groupoids C} (h : V ⟶ U) (f : U ⟶ X)
    [∀ G : V.totalᵒᵖ ⥤ AddCommGrpCat.{wA}, HasRightKanExtension (toFunctor h).op G]
    [∀ G : U.totalᵒᵖ ⥤ AddCommGrpCat.{wA}, HasRightKanExtension (toFunctor f).op G]
    [∀ G : V.totalᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension ((toFunctor h).op ⋙ (toFunctor f).op) G]
    [∀ G : V.totalᵒᵖ ⥤ AddCommGrpCat.{wA}, HasRightKanExtension (toFunctor (h ≫ f)).op G] :
    ((toFunctor (h ≫ f)).op.ran :
        (V.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) ⥤ (X.totalᵒᵖ ⥤ AddCommGrpCat.{wA})) ≅
      ((toFunctor h).op.ran ⋙ (toFunctor f).op.ran :
        (V.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) ⥤ (X.totalᵒᵖ ⥤ AddCommGrpCat.{wA})) :=
  (conjugateIsoEquiv
      (((toFunctor h).op ⋙ (toFunctor f).op).ranAdjunction AddCommGrpCat.{wA})
      ((toFunctor (h ≫ f)).op.ranAdjunction AddCommGrpCat.{wA})
      (presheafInverseImage_compIso h f AddCommGrpCat.{wA})).symm ≪≫
    Functor.ranCompIso (toFunctor h).op (toFunctor f).op

/-- The pullback map `f_* ⟶ h⁻¹ ⋙ (h ≫ f)_*` of abelian-group-valued presheaves
attached to a commutative triangle `V ⟶ U ⟶ X`. -/
def pullbackMap {V : FiberedCategoryOver.Groupoids C} (h : V ⟶ U) (f : U ⟶ X)
    [∀ G : V.totalᵒᵖ ⥤ AddCommGrpCat.{wA}, HasRightKanExtension (toFunctor h).op G]
    [∀ G : U.totalᵒᵖ ⥤ AddCommGrpCat.{wA}, HasRightKanExtension (toFunctor f).op G]
    [∀ G : V.totalᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension ((toFunctor h).op ⋙ (toFunctor f).op) G]
    [∀ G : V.totalᵒᵖ ⥤ AddCommGrpCat.{wA}, HasRightKanExtension (toFunctor (h ≫ f)).op G] :
    ((toFunctor f).op.ran :
        (U.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) ⥤ (X.totalᵒᵖ ⥤ AddCommGrpCat.{wA})) ⟶
      presheafInverseImage (toFunctor h) AddCommGrpCat.{wA} ⋙
        ((toFunctor (h ≫ f)).op.ran :
          (V.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) ⥤ (X.totalᵒᵖ ⥤ AddCommGrpCat.{wA})) :=
  whiskerRight ((toFunctor h).op.ranAdjunction AddCommGrpCat.{wA}).unit (toFunctor f).op.ran ≫
    whiskerLeft (presheafInverseImage (toFunctor h) AddCommGrpCat.{wA})
      (pushforwardCompIso h f).inv

/-- Component of `pullbackMap` at a presheaf `G` on `U`. -/
theorem pullbackMap_app {V : FiberedCategoryOver.Groupoids C} (h : V ⟶ U) (f : U ⟶ X)
    [∀ G : V.totalᵒᵖ ⥤ AddCommGrpCat.{wA}, HasRightKanExtension (toFunctor h).op G]
    [∀ G : U.totalᵒᵖ ⥤ AddCommGrpCat.{wA}, HasRightKanExtension (toFunctor f).op G]
    [∀ G : V.totalᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension ((toFunctor h).op ⋙ (toFunctor f).op) G]
    [∀ G : V.totalᵒᵖ ⥤ AddCommGrpCat.{wA}, HasRightKanExtension (toFunctor (h ≫ f)).op G]
    (G : U.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) :
    (pullbackMap h f).app G =
      (toFunctor f).op.ran.map (((toFunctor h).op.ranAdjunction AddCommGrpCat.{wA}).unit.app G) ≫
        (pushforwardCompIso h f).inv.app
          ((presheafInverseImage (toFunctor h) AddCommGrpCat.{wA}).obj G) :=
  sorry

/-- `pullbackMap` is whiskering of the `ranAdjunction` unit of `h` by `f_*`,
followed by `(pushforwardCompIso h f).inv`. -/
theorem pullbackMap_eq {V : FiberedCategoryOver.Groupoids C} (h : V ⟶ U) (f : U ⟶ X)
    [∀ G : V.totalᵒᵖ ⥤ AddCommGrpCat.{wA}, HasRightKanExtension (toFunctor h).op G]
    [∀ G : U.totalᵒᵖ ⥤ AddCommGrpCat.{wA}, HasRightKanExtension (toFunctor f).op G]
    [∀ G : V.totalᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension ((toFunctor h).op ⋙ (toFunctor f).op) G]
    [∀ G : V.totalᵒᵖ ⥤ AddCommGrpCat.{wA}, HasRightKanExtension (toFunctor (h ≫ f)).op G] :
    pullbackMap h f =
      whiskerRight ((toFunctor h).op.ranAdjunction AddCommGrpCat.{wA}).unit (toFunctor f).op.ran ≫
        whiskerLeft (presheafInverseImage (toFunctor h) AddCommGrpCat.{wA})
          (pushforwardCompIso h f).inv :=
  sorry

/-- The `n`-th term of the relative Čech complex: `f_{n,*} f_n⁻¹ F`. -/
def term (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) (n : SimplexCategory)
    [∀ G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (apexFunctor f n).op G] :
    X.totalᵒᵖ ⥤ AddCommGrpCat.{wA} :=
  (apexFunctor f n).op.ran.obj ((apexFunctor f n).op ⋙ F)

/-- Degree `n` of the relative Čech complex is `f_{n,*} f_n⁻¹ F`. -/
theorem term_eq (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) (n : SimplexCategory)
    [∀ G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (apexFunctor f n).op G] :
    term f F n = (apexFunctor f n).op.ran.obj ((apexFunctor f n).op ⋙ F) :=
  rfl

/-- Composition of right Kan extensions along reindexing and the apex functor. -/
def reindex_apex_ranCompIso (f : U ⟶ X) {m n : SimplexCategory} (φ : m ⟶ n)
    [∀ G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}, HasRightKanExtension (reindex φ).op G]
    [∀ G : (Simplex.Obj f m)ᵒᵖ ⥤ AddCommGrpCat.{wA}, HasRightKanExtension (apexFunctor f m).op G]
    [∀ G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension ((reindex φ).op ⋙ (apexFunctor f m).op) G] :
    (((reindex φ).op ⋙ (apexFunctor f m).op).ran :
        ((Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}) ⥤
          (X.totalᵒᵖ ⥤ AddCommGrpCat.{wA})) ≅
      ((reindex φ).op.ran ⋙ (apexFunctor f m).op.ran) :=
  Functor.ranCompIso (reindex φ).op (apexFunctor f m).op

/-- Coface operator of relative Čech terms along a morphism of simplices. -/
def coface (f : U ⟶ X) {m n : SimplexCategory} (φ : m ⟶ n)
    [∀ G : (Simplex.Obj f m)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (apexFunctor f m).op G]
    [∀ G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (reindex φ).op G]
    [∀ G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension ((reindex φ).op ⋙ (apexFunctor f m).op) G] :
    (apexFunctor f m).op.ran ⟶
      presheafInverseImage (reindex φ) AddCommGrpCat.{wA} ⋙
        ((reindex φ).op ⋙ (apexFunctor f m).op).ran :=
  whiskerRight ((reindex φ).op.ranAdjunction AddCommGrpCat.{wA}).unit
      (apexFunctor f m).op.ran ≫
    whiskerLeft (presheafInverseImage (reindex φ) AddCommGrpCat.{wA})
      (reindex_apex_ranCompIso f φ).inv

/-- After reindexing, the coface target is the degree-`n` relative Čech term. -/
theorem coface_app_target_eq (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA})
    {m n : SimplexCategory} (φ : m ⟶ n)
    [∀ G : (Simplex.Obj f m)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (apexFunctor f m).op G]
    [∀ G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (apexFunctor f n).op G]
    [∀ G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (reindex φ).op G]
    [∀ G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension ((reindex φ).op ⋙ (apexFunctor f m).op) G] :
    (((reindex φ).op ⋙ (apexFunctor f m).op).ran.obj
        ((reindex φ).op ⋙ ((apexFunctor f m).op ⋙ F))) =
      term f F n :=
  sorry

/-- Degreewise coface `f_{m,*} f_m⁻¹ F ⟶ f_{n,*} f_n⁻¹ F`. -/
def cofaceApp (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA})
    {m n : SimplexCategory} (φ : m ⟶ n)
    [∀ G : (Simplex.Obj f m)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (apexFunctor f m).op G]
    [∀ G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (apexFunctor f n).op G]
    [∀ G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (reindex φ).op G]
    [∀ G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension ((reindex φ).op ⋙ (apexFunctor f m).op) G] :
    term f F m ⟶ term f F n :=
  (coface f φ).app ((apexFunctor f m).op ⋙ F) ≫ eqToHom (coface_app_target_eq f F φ)

/-- The cosimplicial abelian presheaf `n ↦ f_{n,*} f_n⁻¹ F` on `X`. -/
def cosimplicial (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA})
    [∀ (n : SimplexCategory) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (apexFunctor f n).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (reindex φ).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension ((reindex φ).op ⋙ (apexFunctor f m).op) G] :
    CosimplicialObject (X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) where
  obj n := term f F n
  map φ := cofaceApp f F φ
  map_id := sorry
  map_comp := sorry

/-- The relative Čech complex `K^•(f, F)` of abelian presheaves on `X`. -/
def complex (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA})
    [∀ (n : SimplexCategory) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (apexFunctor f n).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (reindex φ).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension ((reindex φ).op ⋙ (apexFunctor f m).op) G] :
    CochainComplex (X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) ℕ :=
  (alternatingCofaceMapComplex _).obj (cosimplicial f F)

/-- Degree `n` of `RelativeCech.complex` is `f_{n,*} f_n⁻¹ F`. -/
theorem complex_X (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) (n : ℕ)
    [∀ (n : SimplexCategory) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (apexFunctor f n).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (reindex φ).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension ((reindex φ).op ⋙ (apexFunctor f m).op) G] :
    (complex f F).X n = term f F ⦋n⦌ :=
  rfl

/-- The relative Čech differential is the alternating sum of coface maps. -/
theorem complex_d (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) (n : ℕ)
    [∀ (n : SimplexCategory) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (apexFunctor f n).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (reindex φ).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension ((reindex φ).op ⋙ (apexFunctor f m).op) G] :
    (complex f F).d n (n + 1) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (cosimplicial f F).δ i :=
  sorry

variable {Y : FiberedCategoryOver.Groupoids C}

/-- Inverse image of a complex of abelian presheaves along a 1-morphism. -/
def inverseImageComplex (e : Y ⟶ X) (K : CochainComplex (X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) ℕ) :
    CochainComplex (Y.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) ℕ :=
  ((presheafInverseImage (toFunctor e) AddCommGrpCat.{wA}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K

/-- Degree `n` of `inverseImageComplex e K` is the inverse image of the degree-`n` term. -/
theorem inverseImageComplex_X (e : Y ⟶ X)
    (K : CochainComplex (X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) ℕ) (n : ℕ) :
    (inverseImageComplex e K).X n =
      (presheafInverseImage (toFunctor e) AddCommGrpCat.{wA}).obj (K.X n) :=
  rfl

end CategoryTheory.FiberedCategoryOver.Groupoids.RelativeCech
