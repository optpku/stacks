/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Cech.Comparison
public import ReasLib.CategoryTheory.Fibered.Groupoids.RelativeCech.Complex

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
variable {U X V Y : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}

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
      HasRightKanExtension (apexFunctor g ⦋n⦌ ⋙ toFunctor e).op G]
    [∀ G : Y.totalᵒᵖ ⥤ AddCommGrpCat.{wA}, HasRightKanExtension (toFunctor e).op G] :
    term f F ⦋n⦌ ⟶
      (toFunctor e).op.ran.obj (term g (Cech.inverseImage e F) ⦋n⦌) :=
  (presheafPullbackMap (A := AddCommGrpCat.{wA}) (coveringMapFunctor t ⦋n⦌) (apexFunctor f ⦋n⦌)
    (g := apexFunctor g ⦋n⦌ ⋙ toFunctor e)
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro P Q a
      change (toFunctor e).map a.apex ≫ 𝟙 _ = 𝟙 _ ≫ (toFunctor e).map a.apex
      simp))).app
      ((apexFunctor f ⦋n⦌).op ⋙ F) ≫
    (presheafPushforwardCompIso (A := AddCommGrpCat.{wA}) (apexFunctor g ⦋n⦌) (toFunctor e)
      (Iso.refl _)).hom.app ((apexFunctor g ⦋n⦌).op ⋙ Cech.inverseImage e F)

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
      HasRightKanExtension (apexFunctor g ⦋n⦌ ⋙ toFunctor e).op G]
    [∀ G : Y.totalᵒᵖ ⥤ AddCommGrpCat.{wA}, HasRightKanExtension (toFunctor e).op G] :
    (presheafInverseImage (toFunctor e) AddCommGrpCat.{wA}).obj (term f F ⦋n⦌) ⟶
      term g (Cech.inverseImage e F) ⦋n⦌ :=
  (((toFunctor e).op.ranAdjunction AddCommGrpCat.{wA}).homEquiv
      (term f F ⦋n⦌) (term g (Cech.inverseImage e F) ⦋n⦌)).symm
    (map_f_toPushforward t F n)

/-- The degreewise square comparison commutes with the relative Čech differentials. -/
theorem map_f_comm {f : U ⟶ X} {g : V ⟶ Y} {h : V ⟶ U} {e : Y ⟶ X} (t : h ≫ f ≅ g ≫ e)
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
      HasRightKanExtension (apexFunctor g n ⋙ toFunctor e).op G]
    [∀ G : Y.totalᵒᵖ ⥤ AddCommGrpCat.{wA}, HasRightKanExtension (toFunctor e).op G] (i j : ℕ) :
    map_f t F i ≫ (complex g (Cech.inverseImage e F)).d i j =
      (inverseImageComplex e (complex f F)).d i j ≫ map_f t F j :=
  sorry

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
      HasRightKanExtension (apexFunctor g n ⋙ toFunctor e).op G]
    [∀ G : Y.totalᵒᵖ ⥤ AddCommGrpCat.{wA}, HasRightKanExtension (toFunctor e).op G] :
    inverseImageComplex e (complex f F) ⟶ complex g (Cech.inverseImage e F) where
  f n := map_f t F n
  comm' := fun i j _ ↦ map_f_comm t F i j

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
      HasRightKanExtension (apexFunctor g n ⋙ toFunctor e).op G]
    [∀ G : Y.totalᵒᵖ ⥤ AddCommGrpCat.{wA}, HasRightKanExtension (toFunctor e).op G] :
    (map t F).f n = map_f t F n :=
  rfl

/-- If `h` and `e` are equivalences, the relative Čech comparison is an isomorphism. -/
instance map_isIso {f : U ⟶ X} {g : V ⟶ Y} {h : V ⟶ U} {e : Y ⟶ X} (t : h ≫ f ≅ g ≫ e)
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA})
    [hh : BasedFunctor.IsEquivalence (toBasedFunctor h)]
    [he : BasedFunctor.IsEquivalence (toBasedFunctor e)]
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
      HasRightKanExtension (apexFunctor g n ⋙ toFunctor e).op G]
    [∀ G : Y.totalᵒᵖ ⥤ AddCommGrpCat.{wA}, HasRightKanExtension (toFunctor e).op G] :
    IsIso (map t F) :=
  sorry

/-- The canonical pullback between relative terms induced by a two-isomorphism. -/
def twoIsoMap_f {f f' : U ⟶ X} (t : f ≅ f') (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) (n : ℕ)
    [∀ G : (Simplex.Obj f ⦋n⦌)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (apexFunctor f ⦋n⦌).op G]
    [∀ G : (Simplex.Obj f' ⦋n⦌)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (apexFunctor f' ⦋n⦌).op G]
    [∀ G : (Simplex.Obj f' ⦋n⦌)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (twoIsoReindex t ⦋n⦌).op G]
    [∀ G : (Simplex.Obj f' ⦋n⦌)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension ((twoIsoReindex t ⦋n⦌).op ⋙ (apexFunctor f ⦋n⦌).op) G] :
    term f F ⦋n⦌ ⟶ term f' F ⦋n⦌ :=
  (presheafPullbackMap (A := AddCommGrpCat.{wA}) (twoIsoReindex t ⦋n⦌) (apexFunctor f ⦋n⦌)
    (g := apexFunctor f' ⦋n⦌)
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro P Q a
      change a.apex ≫ 𝟙 _ = 𝟙 _ ≫ a.apex
      simp))).app
      ((apexFunctor f ⦋n⦌).op ⋙ F)

/-- The pullbacks induced by a two-isomorphism and its inverse compose to the identity. -/
theorem twoIsoMap_f_hom_inv_id {f f' : U ⟶ X} (t : f ≅ f') (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) (n : ℕ)
    [∀ G : (Simplex.Obj f ⦋n⦌)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (apexFunctor f ⦋n⦌).op G]
    [∀ G : (Simplex.Obj f' ⦋n⦌)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (apexFunctor f' ⦋n⦌).op G]
    [∀ G : (Simplex.Obj f' ⦋n⦌)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (twoIsoReindex t ⦋n⦌).op G]
    [∀ G : (Simplex.Obj f' ⦋n⦌)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension ((twoIsoReindex t ⦋n⦌).op ⋙ (apexFunctor f ⦋n⦌).op) G]
    [backwardRan : ∀ G : (Simplex.Obj f ⦋n⦌)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (twoIsoReindex t.symm ⦋n⦌).op G]
    [backwardApexRan : ∀ G : (Simplex.Obj f ⦋n⦌)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension ((twoIsoReindex t.symm ⦋n⦌).op ⋙ (apexFunctor f' ⦋n⦌).op) G] :
    twoIsoMap_f t F n ≫ twoIsoMap_f t.symm F n = 𝟙 (term f F ⦋n⦌) :=
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
  hom := twoIsoMap_f t F n
  inv := twoIsoMap_f t.symm F n
  hom_inv_id := twoIsoMap_f_hom_inv_id t F n
  inv_hom_id := twoIsoMap_f_hom_inv_id t.symm F n
    (backwardRan := inferInstanceAs (∀ G : (Simplex.Obj f' ⦋n⦌)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (twoIsoReindex t ⦋n⦌).op G))
    (backwardApexRan := inferInstanceAs (∀ G : (Simplex.Obj f' ⦋n⦌)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension ((twoIsoReindex t ⦋n⦌).op ⋙ (apexFunctor f ⦋n⦌).op) G))

/-- The canonical two-isomorphism pullbacks commute with the relative Čech differentials. -/
theorem twoIsoMap_f_comm {f f' : U ⟶ X} (t : f ≅ f') (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA})
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
      HasRightKanExtension ((twoIsoReindex t.symm n).op ⋙ (apexFunctor f' n).op) G] (i j : ℕ) :
    twoIsoMap_f t F i ≫ (complex f' F).d i j =
      (complex f F).d i j ≫ twoIsoMap_f t F j :=
  sorry

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
  HomologicalComplex.Hom.isoOfComponents (fun n ↦ isoOfTwoIsoX t F n)
    (fun i j _ ↦ twoIsoMap_f_comm t F i j)

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
