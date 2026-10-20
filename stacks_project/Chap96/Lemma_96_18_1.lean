/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Cech.Comparison

/-!
# Generalities on Čech complexes of categories fibred in groupoids

A 2-commutative square of categories fibred in groupoids over `(Sch/S)_fppf`
induces a morphism of Čech complexes, which is an isomorphism when the
horizontal arrows are equivalences; 2-isomorphic 1-morphisms have isomorphic
Čech complexes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor FiberedCategoryOver.Groupoids
open scoped Bicategory Simplicial

noncomputable section

universe u

variable {S : Scheme.{u}} {U X : GroupoidsOver S}

variable {V Y : GroupoidsOver S}
variable {f : U ⟶ X} {g : V ⟶ Y} {h : V ⟶ U} {e : Y ⟶ X}

/- Lemma 96.18.1 (1): a two-commutative square induces the canonical morphism
of Čech complexes for an abelian presheaf. -/
@[stacks 06X5] #check (CategoryTheory.FiberedCategoryOver.Groupoids.Cech.map :
  (t : h ≫ f ≅ g ≫ e) → (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) →
    Cech.complex f F ⟶ Cech.complex g (Cech.inverseImage e F))

/- The degreewise map is pullback along the explicit covering-simplex comparison. -/
#check (CategoryTheory.FiberedCategoryOver.Groupoids.Cech.map_app :
  ∀ (t : h ≫ f ≅ g ≫ e) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ),
    (Cech.map t F).f n =
      Cech.globalSectionsMap (Cech.coveringMapFunctor t ⦋n⦌)
        ((Cech.apexFunctor f ⦋n⦌).op ⋙ F))

/- Lemma 96.18.1 (2): equivalences on the horizontal arrows make the canonical
comparison an isomorphism. -/
@[stacks 06X5] #check (CategoryTheory.FiberedCategoryOver.Groupoids.Cech.map_isIso :
  ∀ (t : h ≫ f ≅ g ≫ e) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    [hh : BasedFunctor.IsEquivalence (toBasedFunctor h)]
    [he : BasedFunctor.IsEquivalence (toBasedFunctor e)], IsIso (Cech.map t F))

/- Lemma 96.18.1 (3): two-isomorphic morphisms have canonically isomorphic
Čech complexes. -/
@[stacks 06X5] #check (CategoryTheory.FiberedCategoryOver.Groupoids.Cech.isoOfTwoIso :
  ∀ {f f' : U ⟶ X} (t : f ≅ f') (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
    Cech.complex f F ≅ Cech.complex f' F)

/- The forward component is the pullback along the two-isomorphism reindexing. -/
#check (CategoryTheory.FiberedCategoryOver.Groupoids.Cech.isoOfTwoIso_hom_app :
  ∀ {f f' : U ⟶ X} (t : f ≅ f') (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ),
    (Cech.isoOfTwoIso t F).hom.f n =
      Cech.globalSectionsMap (Cech.twoIsoReindex t ⦋n⦌)
        ((Cech.apexFunctor f ⦋n⦌).op ⋙ F))

end
