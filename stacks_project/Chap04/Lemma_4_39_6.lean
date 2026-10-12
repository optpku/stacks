/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Setoids.Components.Equivalence
import StacksCheckRecall

@[expose] public section

universe u v

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable (X Y : FiberedCategoryOver.Setoids C)
variable {F G : X ⟶ Y}
variable (h : (FiberedCategoryOver.Setoids.components C).map
    (Bicategory.HomotopyCategory.mkHom F) =
  (FiberedCategoryOver.Setoids.components C).map
    (Bicategory.HomotopyCategory.mkHom G))

/- Lemma 4.39.6 (1): fibrewise `π₀` followed by the discrete Grothendieck construction is a
pseudofunctor to the locally discrete bicategory of categories fibred in sets. -/
@[stacks 04SC "(1)"]
#check (FiberedCategoryOver.Setoids.components.pseudofunctor C :
  FiberedCategoryOver.Setoids C ⥤ᵖ
    LocallyDiscrete (FiberedCategoryOver.Sets C))

/- Lemma 4.39.6 (2): equal maps on fibrewise components come from a unique `2`-isomorphism. -/
@[stacks 04SC "(2)"]
#check (FiberedCategoryOver.Setoids.components.uniqueIso_of_map_eq h :
  Nonempty (F ≅ G) ∧ Subsingleton (F ≅ G))

/- Lemma 4.39.6 (3): every morphism between associated categories fibred in sets is induced by a
`1`-morphism of the original categories fibred in setoids. -/
@[stacks 04SC "(3)"]
#check (FiberedCategoryOver.Setoids.components.map_surjective X Y :
  Function.Surjective (fun F : X ⟶ Y ↦
    (FiberedCategoryOver.Setoids.components C).map
      (Bicategory.HomotopyCategory.mkHom F)))

/- Lemma 4.39.6 (4): every category fibred in sets is in the essential image of fibrewise
components. -/
@[stacks 04SC "(4)"]
#check (FiberedCategoryOver.Setoids.components.essSurj C :
  (FiberedCategoryOver.Setoids.components C).EssSurj)

/- Lemma 4.39.6 (5): homs modulo `2`-isomorphism are the homs of fibrewise-component
presheaves. -/
@[stacks 04SC "(5)"]
#check (FiberedCategoryOver.Setoids.componentsPresheaf.map_bijective X Y :
  Function.Bijective
    ((FiberedCategoryOver.Setoids.componentsPresheaf C).map :
      (Bicategory.HomotopyCategory.mk X ⟶
        Bicategory.HomotopyCategory.mk Y) →
      (Functor.fiberIsoClassPresheaf X.p ⟶
        Functor.fiberIsoClassPresheaf Y.p)))

end CategoryTheory
