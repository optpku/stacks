module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.UnderlyingFunctorIso
public import ReasLib.CategoryTheory.Sites.Presheaf.InverseImage
public import stacks_project.Chap96.Lemma_96_18_1_Cech

/-!
# Functoriality of Čech complexes of categories fibred in groupoids

A 2-commutative square induces a morphism of Čech complexes; equivalences on the
horizontal arrows make it an isomorphism; 2-isomorphic 1-morphisms have isomorphic
Čech complexes.
-/

@[expose] public section

open CategoryTheory AlgebraicTopology Functor
open scoped Bicategory Simplicial

noncomputable section

universe u v w vS wA

namespace CategoryTheory.FiberedCategoryOver.Groupoids.Cech

variable {C : Type u} [Category.{v} C]
variable {U X V Y : FiberedCategoryOver.Groupoids C}

/-- Inverse image of an abelian presheaf along a 1-morphism of categories fibred in
groupoids. -/
abbrev inverseImage (e : Y ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) :
    Y.totalᵒᵖ ⥤ AddCommGrpCat.{wA} :=
  (presheafInverseImage (toFunctor e) AddCommGrpCat.{wA}).obj F

/-- The total-category functor `V_n ⥤ U_n` induced by a 2-commutative square. -/
def coveringMapFunctor {f : U ⟶ X} {g : V ⟶ Y} {h : V ⟶ U} {e : Y ⟶ X}
    (t : h ≫ f ≅ g ≫ e) (n : SimplexCategory) :
    Simplex.Obj g n ⥤ Simplex.Obj f n where
  obj P :=
    Simplex.objMk (fun i ↦ (toFunctor h).obj (P.vertices i)) ((toFunctor e).obj P.apex)
      (fun i ↦ (toFunctorIso t).app (P.vertices i) ≪≫ (toFunctor e).mapIso (P.iso i))
  map ψ :=
    Simplex.homMk (fun i ↦ (toFunctor h).map (ψ.vertex i)) ((toFunctor e).map ψ.apex) sorry
  map_id := sorry
  map_comp := sorry

/-- The 1-morphism `V_n ⟶ U_n` induced by a 2-commutative square. -/
def coveringMap {f : U ⟶ X} {g : V ⟶ Y} {h : V ⟶ U} {e : Y ⟶ X}
    (t : h ≫ f ≅ g ≫ e) (n : SimplexCategory) :
    covering g n ⟶ covering f n :=
  ofBasedFunctor
    { toFunctor := coveringMapFunctor t n
      w := sorry }

/-- If `h` and `e` are equivalences, then `V_n ⟶ U_n` is an equivalence. -/
theorem coveringMap_isEquivalence {f : U ⟶ X} {g : V ⟶ Y} {h : V ⟶ U} {e : Y ⟶ X}
    (t : h ≫ f ≅ g ≫ e) (n : SimplexCategory)
    (hh : BasedFunctor.IsEquivalence (toBasedFunctor h))
    (he : BasedFunctor.IsEquivalence (toBasedFunctor e)) :
    BasedFunctor.IsEquivalence (toBasedFunctor (coveringMap t n)) := sorry

/-- The cosimplicial comparison induced by a 2-commutative square. -/
def cosimplicialMap {f : U ⟶ X} {g : V ⟶ Y} {h : V ⟶ U} {e : Y ⟶ X}
    (t : h ≫ f ≅ g ≫ e) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) :
    cosimplicial f F ⟶ cosimplicial g (inverseImage e F) where
  app n := globalSectionsMap (coveringMapFunctor t n) ((apexFunctor f n).op ⋙ F)
  naturality := sorry

/-- The morphism of Čech complexes induced by a 2-commutative square of categories
fibred in groupoids. -/
def map {f : U ⟶ X} {g : V ⟶ Y} {h : V ⟶ U} {e : Y ⟶ X}
    (t : h ≫ f ≅ g ≫ e) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) :
    complex f F ⟶ complex g (inverseImage e F) :=
  (alternatingCofaceMapComplex _).map (cosimplicialMap t F)

/-- Degree `n` of `Cech.map` is pullback of global sections along `V_n ⟶ U_n`. -/
theorem map_app {f : U ⟶ X} {g : V ⟶ Y} {h : V ⟶ U} {e : Y ⟶ X}
    (t : h ≫ f ≅ g ≫ e) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) (n : ℕ) :
    (map t F).f n =
      globalSectionsMap (coveringMapFunctor t ⦋n⦌) ((apexFunctor f ⦋n⦌).op ⋙ F) := sorry

/-- If `h` and `e` are equivalences, the Čech comparison is an isomorphism. -/
theorem map_isIso {f : U ⟶ X} {g : V ⟶ Y} {h : V ⟶ U} {e : Y ⟶ X}
    (t : h ≫ f ≅ g ≫ e) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA})
    (hh : BasedFunctor.IsEquivalence (toBasedFunctor h))
    (he : BasedFunctor.IsEquivalence (toBasedFunctor e)) :
    IsIso (map t F) := sorry

/-- Reindexing of covering simplices along a 2-isomorphism of 1-morphisms. -/
def twoIsoReindex {f f' : U ⟶ X} (t : f ≅ f') (n : SimplexCategory) :
    Simplex.Obj f' n ⥤ Simplex.Obj f n where
  obj P :=
    Simplex.objMk P.vertices P.apex
      (fun i ↦ (toFunctorIso t).app (P.vertices i) ≪≫ P.iso i)
  map ψ := Simplex.homMk ψ.vertex ψ.apex sorry
  map_id := sorry
  map_comp := sorry

/-- Degreewise isomorphism of Čech terms induced by a 2-isomorphism of 1-morphisms. -/
def isoOfTwoIsoX {f f' : U ⟶ X} (t : f ≅ f') (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA})
    (n : ℕ) : (complex f F).X n ≅ (complex f' F).X n where
  hom := globalSectionsMap (twoIsoReindex t ⦋n⦌) ((apexFunctor f ⦋n⦌).op ⋙ F)
  inv := globalSectionsMap (twoIsoReindex t.symm ⦋n⦌) ((apexFunctor f' ⦋n⦌).op ⋙ F)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- If `f, f' : U ⟶ X` are 2-isomorphic, the associated Čech complexes are
canonically isomorphic. -/
def isoOfTwoIso {f f' : U ⟶ X} (t : f ≅ f') (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) :
    complex f F ≅ complex f' F :=
  HomologicalComplex.Hom.isoOfComponents (fun n ↦ isoOfTwoIsoX t F n) sorry

end CategoryTheory.FiberedCategoryOver.Groupoids.Cech
