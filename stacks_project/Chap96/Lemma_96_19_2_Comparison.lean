/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import stacks_project.Chap96.Lemma_96_18_1_Comparison
public import stacks_project.Chap96.Lemma_96_19_2_RelativeCech

/-!
# Functoriality of relative Čech complexes

A 2-commutative square induces a morphism
`e⁻¹ K^•(f, F) ⟶ K^•(g, e⁻¹ F)`; equivalences on the horizontal arrows
make it an isomorphism; 2-isomorphic 1-morphisms have isomorphic relative
Čech complexes.
-/

@[expose] public section

open CategoryTheory AlgebraicTopology Functor
open scoped Bicategory Simplicial

noncomputable section

universe u v w vS wA

namespace CategoryTheory.FiberedCategoryOver.Groupoids.RelativeCech

open Cech

variable {C : Type u} [Category.{v} C]
variable {U X V Y : FiberedCategoryOver.Groupoids C}

/-- Composition of right Kan extensions along `V_n ⟶ U_n` and the apex of `U_n`. -/
def coveringMap_apex_ranCompIso {f : U ⟶ X} {g : V ⟶ Y} {h : V ⟶ U} {e : Y ⟶ X}
    (t : h ≫ f ≅ g ≫ e) (n : SimplexCategory)
    [∀ G : (Simplex.Obj g n)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (coveringMapFunctor t n).op G]
    [∀ G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (apexFunctor f n).op G]
    [∀ G : (Simplex.Obj g n)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension ((coveringMapFunctor t n).op ⋙ (apexFunctor f n).op) G] :
    (((coveringMapFunctor t n).op ⋙ (apexFunctor f n).op).ran :
        ((Simplex.Obj g n)ᵒᵖ ⥤ AddCommGrpCat.{wA}) ⥤
          (X.totalᵒᵖ ⥤ AddCommGrpCat.{wA})) ≅
      ((coveringMapFunctor t n).op.ran ⋙ (apexFunctor f n).op.ran) :=
  Functor.ranCompIso (coveringMapFunctor t n).op (apexFunctor f n).op

/-- Pullback of `f_{n,*}` along the covering-simplex functor `V_n ⥤ U_n`. -/
def coveringPullback {f : U ⟶ X} {g : V ⟶ Y} {h : V ⟶ U} {e : Y ⟶ X}
    (t : h ≫ f ≅ g ≫ e) (n : SimplexCategory)
    [∀ G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (apexFunctor f n).op G]
    [∀ G : (Simplex.Obj g n)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (coveringMapFunctor t n).op G]
    [∀ G : (Simplex.Obj g n)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension ((coveringMapFunctor t n).op ⋙ (apexFunctor f n).op) G] :
    (apexFunctor f n).op.ran ⟶
      presheafInverseImage (coveringMapFunctor t n) AddCommGrpCat.{wA} ⋙
        ((coveringMapFunctor t n).op ⋙ (apexFunctor f n).op).ran :=
  whiskerRight ((coveringMapFunctor t n).op.ranAdjunction AddCommGrpCat.{wA}).unit
      (apexFunctor f n).op.ran ≫
    whiskerLeft (presheafInverseImage (coveringMapFunctor t n) AddCommGrpCat.{wA})
      (coveringMap_apex_ranCompIso t n).inv

/-- The covering-simplex functor `V_n ⥤ U_n` followed by the apex of `U_n` equals
the apex of `V_n` followed by `e`. Both send a simplex to `e(apex)` and a morphism
to `e(apex map)`. -/
theorem coveringMap_comp_apex_eq {f : U ⟶ X} {g : V ⟶ Y} {h : V ⟶ U} {e : Y ⟶ X}
    (t : h ≫ f ≅ g ≫ e) (n : SimplexCategory) :
    coveringMapFunctor t n ⋙ apexFunctor f n = apexFunctor g n ⋙ toFunctor e :=
  sorry

/-- Right Kan extension along `c ⋙ f_n` agrees with right Kan extension along
`g_n ≫ e` after `coveringMap_comp_apex_eq`. -/
theorem coveringMap_comp_apex_ran_eq {f : U ⟶ X} {g : V ⟶ Y} {h : V ⟶ U} {e : Y ⟶ X}
    (t : h ≫ f ≅ g ≫ e) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) (n : ℕ)
    [∀ G : (Simplex.Obj g ⦋n⦌)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension ((coveringMapFunctor t ⦋n⦌).op ⋙ (apexFunctor f ⦋n⦌).op) G]
    [∀ G : (Simplex.Obj g ⦋n⦌)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension ((apexFunctor g ⦋n⦌).op ⋙ (toFunctor e).op) G] :
    ((coveringMapFunctor t ⦋n⦌).op ⋙ (apexFunctor f ⦋n⦌).op).ran.obj
        ((coveringMapFunctor t ⦋n⦌).op ⋙ ((apexFunctor f ⦋n⦌).op ⋙ F)) =
      ((apexFunctor g ⦋n⦌).op ⋙ (toFunctor e).op).ran.obj
        ((apexFunctor g ⦋n⦌).op ⋙ Cech.inverseImage e F) :=
  sorry

/-- Degree `n` comparison on `X` before taking the mate:
`f_{n,*} f_n⁻¹ F ⟶ e_* (g_{n,*} g_n⁻¹ (e⁻¹ F))`. -/
def map_f_toPushforward {f : U ⟶ X} {g : V ⟶ Y} {h : V ⟶ U} {e : Y ⟶ X}
    (t : h ≫ f ≅ g ≫ e) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) (n : ℕ)
    [∀ G : (Simplex.Obj f ⦋n⦌)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (apexFunctor f ⦋n⦌).op G]
    [∀ G : (Simplex.Obj g ⦋n⦌)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (apexFunctor g ⦋n⦌).op G]
    [∀ G : (Simplex.Obj g ⦋n⦌)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (coveringMapFunctor t ⦋n⦌).op G]
    [∀ G : (Simplex.Obj g ⦋n⦌)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension ((coveringMapFunctor t ⦋n⦌).op ⋙ (apexFunctor f ⦋n⦌).op) G]
    [∀ G : (Simplex.Obj g ⦋n⦌)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension ((apexFunctor g ⦋n⦌).op ⋙ (toFunctor e).op) G]
    [∀ G : Y.totalᵒᵖ ⥤ AddCommGrpCat.{wA}, HasRightKanExtension (toFunctor e).op G] :
    term f F ⦋n⦌ ⟶
      (toFunctor e).op.ran.obj (term g (Cech.inverseImage e F) ⦋n⦌) :=
  (coveringPullback t ⦋n⦌).app ((apexFunctor f ⦋n⦌).op ⋙ F) ≫
    eqToHom (coveringMap_comp_apex_ran_eq t F n) ≫
    (ranCompIso (apexFunctor g ⦋n⦌).op (toFunctor e).op).hom.app
      ((apexFunctor g ⦋n⦌).op ⋙ Cech.inverseImage e F)

/-- Degree `n` comparison `e⁻¹ (f_{n,*} f_n⁻¹ F) ⟶ g_{n,*} g_n⁻¹ (e⁻¹ F)`,
the `ranAdjunction` mate of `map_f_toPushforward`. -/
def map_f {f : U ⟶ X} {g : V ⟶ Y} {h : V ⟶ U} {e : Y ⟶ X} (t : h ≫ f ≅ g ≫ e)
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) (n : ℕ)
    [∀ G : (Simplex.Obj f ⦋n⦌)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (apexFunctor f ⦋n⦌).op G]
    [∀ G : (Simplex.Obj g ⦋n⦌)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (apexFunctor g ⦋n⦌).op G]
    [∀ G : (Simplex.Obj g ⦋n⦌)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (coveringMapFunctor t ⦋n⦌).op G]
    [∀ G : (Simplex.Obj g ⦋n⦌)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension ((coveringMapFunctor t ⦋n⦌).op ⋙ (apexFunctor f ⦋n⦌).op) G]
    [∀ G : (Simplex.Obj g ⦋n⦌)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension ((apexFunctor g ⦋n⦌).op ⋙ (toFunctor e).op) G]
    [∀ G : Y.totalᵒᵖ ⥤ AddCommGrpCat.{wA}, HasRightKanExtension (toFunctor e).op G] :
    (presheafInverseImage (toFunctor e) AddCommGrpCat.{wA}).obj (term f F ⦋n⦌) ⟶
      term g (Cech.inverseImage e F) ⦋n⦌ :=
  (((toFunctor e).op.ranAdjunction AddCommGrpCat.{wA}).homEquiv
      (term f F ⦋n⦌) (term g (Cech.inverseImage e F) ⦋n⦌)).symm
    (map_f_toPushforward t F n)

/-- The morphism of relative Čech complexes induced by a 2-commutative square. -/
def map {f : U ⟶ X} {g : V ⟶ Y} {h : V ⟶ U} {e : Y ⟶ X} (t : h ≫ f ≅ g ≫ e)
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA})
    [∀ (n : SimplexCategory) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (apexFunctor f n).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (reindex φ).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension ((reindex φ).op ⋙ (apexFunctor f m).op) G]
    [∀ (n : SimplexCategory) (G : (Simplex.Obj g n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (apexFunctor g n).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj g n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (reindex φ).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj g n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension ((reindex φ).op ⋙ (apexFunctor g m).op) G]
    [∀ (n : SimplexCategory) (G : (Simplex.Obj g n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (coveringMapFunctor t n).op G]
    [∀ (n : SimplexCategory) (G : (Simplex.Obj g n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension ((coveringMapFunctor t n).op ⋙ (apexFunctor f n).op) G]
    [∀ (n : SimplexCategory) (G : (Simplex.Obj g n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension ((apexFunctor g n).op ⋙ (toFunctor e).op) G]
    [∀ G : Y.totalᵒᵖ ⥤ AddCommGrpCat.{wA}, HasRightKanExtension (toFunctor e).op G] :
    inverseImageComplex e (complex f F) ⟶ complex g (Cech.inverseImage e F) where
  f n := map_f t F n
  comm' := sorry

/-- Degree `n` of `RelativeCech.map` is the mate of pullback along `V_n ⟶ U_n`. -/
theorem map_app {f : U ⟶ X} {g : V ⟶ Y} {h : V ⟶ U} {e : Y ⟶ X} (t : h ≫ f ≅ g ≫ e)
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) (n : ℕ)
    [∀ (n : SimplexCategory) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (apexFunctor f n).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (reindex φ).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension ((reindex φ).op ⋙ (apexFunctor f m).op) G]
    [∀ (n : SimplexCategory) (G : (Simplex.Obj g n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (apexFunctor g n).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj g n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (reindex φ).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj g n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension ((reindex φ).op ⋙ (apexFunctor g m).op) G]
    [∀ (n : SimplexCategory) (G : (Simplex.Obj g n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (coveringMapFunctor t n).op G]
    [∀ (n : SimplexCategory) (G : (Simplex.Obj g n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension ((coveringMapFunctor t n).op ⋙ (apexFunctor f n).op) G]
    [∀ (n : SimplexCategory) (G : (Simplex.Obj g n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension ((apexFunctor g n).op ⋙ (toFunctor e).op) G]
    [∀ G : Y.totalᵒᵖ ⥤ AddCommGrpCat.{wA}, HasRightKanExtension (toFunctor e).op G] :
    (map t F).f n = map_f t F n :=
  rfl

/-- If `h` and `e` are equivalences, the relative Čech comparison is an isomorphism. -/
theorem map_isIso {f : U ⟶ X} {g : V ⟶ Y} {h : V ⟶ U} {e : Y ⟶ X} (t : h ≫ f ≅ g ≫ e)
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA})
    (hh : BasedFunctor.IsEquivalence (toBasedFunctor h))
    (he : BasedFunctor.IsEquivalence (toBasedFunctor e))
    [∀ (n : SimplexCategory) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (apexFunctor f n).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (reindex φ).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension ((reindex φ).op ⋙ (apexFunctor f m).op) G]
    [∀ (n : SimplexCategory) (G : (Simplex.Obj g n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (apexFunctor g n).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj g n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (reindex φ).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj g n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension ((reindex φ).op ⋙ (apexFunctor g m).op) G]
    [∀ (n : SimplexCategory) (G : (Simplex.Obj g n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (coveringMapFunctor t n).op G]
    [∀ (n : SimplexCategory) (G : (Simplex.Obj g n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension ((coveringMapFunctor t n).op ⋙ (apexFunctor f n).op) G]
    [∀ (n : SimplexCategory) (G : (Simplex.Obj g n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension ((apexFunctor g n).op ⋙ (toFunctor e).op) G]
    [∀ G : Y.totalᵒᵖ ⥤ AddCommGrpCat.{wA}, HasRightKanExtension (toFunctor e).op G] :
    IsIso (map t F) :=
  sorry

/-- Composition of right Kan extensions along 2-isomorphism reindexing and the apex. -/
def twoIso_apex_ranCompIso {f f' : U ⟶ X} (t : f ≅ f') (n : SimplexCategory)
    [∀ G : (Simplex.Obj f' n)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (twoIsoReindex t n).op G]
    [∀ G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (apexFunctor f n).op G]
    [∀ G : (Simplex.Obj f' n)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension ((twoIsoReindex t n).op ⋙ (apexFunctor f n).op) G] :
    (((twoIsoReindex t n).op ⋙ (apexFunctor f n).op).ran :
        ((Simplex.Obj f' n)ᵒᵖ ⥤ AddCommGrpCat.{wA}) ⥤
          (X.totalᵒᵖ ⥤ AddCommGrpCat.{wA})) ≅
      ((twoIsoReindex t n).op.ran ⋙ (apexFunctor f n).op.ran) :=
  Functor.ranCompIso (twoIsoReindex t n).op (apexFunctor f n).op

/-- Pullback of `f_{n,*}` along reindexing by a 2-isomorphism. -/
def twoIsoPullback {f f' : U ⟶ X} (t : f ≅ f') (n : SimplexCategory)
    [∀ G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (apexFunctor f n).op G]
    [∀ G : (Simplex.Obj f' n)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (twoIsoReindex t n).op G]
    [∀ G : (Simplex.Obj f' n)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension ((twoIsoReindex t n).op ⋙ (apexFunctor f n).op) G] :
    (apexFunctor f n).op.ran ⟶
      presheafInverseImage (twoIsoReindex t n) AddCommGrpCat.{wA} ⋙
        ((twoIsoReindex t n).op ⋙ (apexFunctor f n).op).ran :=
  whiskerRight ((twoIsoReindex t n).op.ranAdjunction AddCommGrpCat.{wA}).unit
      (apexFunctor f n).op.ran ≫
    whiskerLeft (presheafInverseImage (twoIsoReindex t n) AddCommGrpCat.{wA})
      (twoIso_apex_ranCompIso t n).inv

/-- The 2-isomorphism reindexing lands in the opposite relative Čech term. -/
theorem twoIsoPullback_target_eq {f f' : U ⟶ X} (t : f ≅ f')
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) (n : ℕ)
    [∀ G : (Simplex.Obj f ⦋n⦌)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (apexFunctor f ⦋n⦌).op G]
    [∀ G : (Simplex.Obj f' ⦋n⦌)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (apexFunctor f' ⦋n⦌).op G]
    [∀ G : (Simplex.Obj f' ⦋n⦌)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (twoIsoReindex t ⦋n⦌).op G]
    [∀ G : (Simplex.Obj f' ⦋n⦌)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension ((twoIsoReindex t ⦋n⦌).op ⋙ (apexFunctor f ⦋n⦌).op) G] :
    ((twoIsoReindex t ⦋n⦌).op ⋙ (apexFunctor f ⦋n⦌).op).ran.obj
        ((twoIsoReindex t ⦋n⦌).op ⋙ ((apexFunctor f ⦋n⦌).op ⋙ F)) =
      term f' F ⦋n⦌ :=
  sorry

/-- Degreewise isomorphism of relative Čech terms induced by a 2-isomorphism. -/
def isoOfTwoIsoX {f f' : U ⟶ X} (t : f ≅ f') (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) (n : ℕ)
    [∀ G : (Simplex.Obj f ⦋n⦌)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (apexFunctor f ⦋n⦌).op G]
    [∀ G : (Simplex.Obj f' ⦋n⦌)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (apexFunctor f' ⦋n⦌).op G]
    [∀ G : (Simplex.Obj f' ⦋n⦌)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (twoIsoReindex t ⦋n⦌).op G]
    [∀ G : (Simplex.Obj f' ⦋n⦌)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension ((twoIsoReindex t ⦋n⦌).op ⋙ (apexFunctor f ⦋n⦌).op) G]
    [∀ G : (Simplex.Obj f ⦋n⦌)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (twoIsoReindex t.symm ⦋n⦌).op G]
    [∀ G : (Simplex.Obj f ⦋n⦌)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension ((twoIsoReindex t.symm ⦋n⦌).op ⋙ (apexFunctor f' ⦋n⦌).op) G] :
    term f F ⦋n⦌ ≅ term f' F ⦋n⦌ where
  hom :=
    (twoIsoPullback t ⦋n⦌).app ((apexFunctor f ⦋n⦌).op ⋙ F) ≫
      eqToHom (twoIsoPullback_target_eq t F n)
  inv :=
    (twoIsoPullback t.symm ⦋n⦌).app ((apexFunctor f' ⦋n⦌).op ⋙ F) ≫
      eqToHom (twoIsoPullback_target_eq t.symm F n)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- If `f, f' : U ⟶ X` are 2-isomorphic, the associated relative Čech complexes are
canonically isomorphic. -/
def isoOfTwoIso {f f' : U ⟶ X} (t : f ≅ f') (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA})
    [∀ (n : SimplexCategory) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (apexFunctor f n).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (reindex φ).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension ((reindex φ).op ⋙ (apexFunctor f m).op) G]
    [∀ (n : SimplexCategory) (G : (Simplex.Obj f' n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (apexFunctor f' n).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj f' n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (reindex φ).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj f' n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension ((reindex φ).op ⋙ (apexFunctor f' m).op) G]
    [∀ (n : SimplexCategory) (G : (Simplex.Obj f' n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (twoIsoReindex t n).op G]
    [∀ (n : SimplexCategory) (G : (Simplex.Obj f' n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension ((twoIsoReindex t n).op ⋙ (apexFunctor f n).op) G]
    [∀ (n : SimplexCategory) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (twoIsoReindex t.symm n).op G]
    [∀ (n : SimplexCategory) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension ((twoIsoReindex t.symm n).op ⋙ (apexFunctor f' n).op) G] :
    complex f F ≅ complex f' F :=
  HomologicalComplex.Hom.isoOfComponents (fun n ↦ isoOfTwoIsoX t F n) sorry

/-- Degree `n` of `isoOfTwoIso` is pullback along the reindexing of covering simplices. -/
theorem isoOfTwoIso_hom_app {f f' : U ⟶ X} (t : f ≅ f')
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) (n : ℕ)
    [∀ (n : SimplexCategory) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (apexFunctor f n).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (reindex φ).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension ((reindex φ).op ⋙ (apexFunctor f m).op) G]
    [∀ (n : SimplexCategory) (G : (Simplex.Obj f' n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (apexFunctor f' n).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj f' n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (reindex φ).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj f' n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension ((reindex φ).op ⋙ (apexFunctor f' m).op) G]
    [∀ (n : SimplexCategory) (G : (Simplex.Obj f' n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (twoIsoReindex t n).op G]
    [∀ (n : SimplexCategory) (G : (Simplex.Obj f' n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension ((twoIsoReindex t n).op ⋙ (apexFunctor f n).op) G]
    [∀ (n : SimplexCategory) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (twoIsoReindex t.symm n).op G]
    [∀ (n : SimplexCategory) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension ((twoIsoReindex t.symm n).op ⋙ (apexFunctor f' n).op) G] :
    (isoOfTwoIso t F).hom.f n = (isoOfTwoIsoX t F n).hom :=
  sorry

end CategoryTheory.FiberedCategoryOver.Groupoids.RelativeCech
