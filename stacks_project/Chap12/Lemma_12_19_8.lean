/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Strict.Composition
public import ReasLib.CategoryTheory.Filtration.Strict.CompositionCounterexample
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u v₁ u₁

namespace CategoryTheory.FilteredObject.Hom

/- Lemma 12.19.8 [05SJ] (1): strict filtered morphisms are not closed under composition in
general. -/
@[stacks 05SJ]
#check (strict_comp_not_in_general :
  ¬ ∀ {C : Type u₁} [Category.{v₁} C] [Abelian C] {A B D : FilteredObject C}
      (f : A ⟶ B) (g : B ⟶ D), Strict f → Strict g → Strict (f ≫ g))

variable {C : Type u} [Category.{v} C] [HasImages C] [HasPullbacks C] [HasEqualizers C]
  [Balanced C]
variable {A B D : FilteredObject C} (f : A ⟶ B) (g : B ⟶ D)

section Mono

variable [Mono g.hom]

/- Lemma 12.19.8 [05SJ] (2): a mono second map makes strictness stable under composition. -/
@[stacks 05SJ]
#check (strict_comp_of_mono f g :
  Strict f → Strict g → Strict (f ≫ g))

end Mono

section Epi

variable [Epi f.hom]

/- Lemma 12.19.8 [05SJ] (3): an epi first map makes strictness stable under composition. -/
@[stacks 05SJ]
#check (strict_comp_of_epi f g :
  Strict f → Strict g → Strict (f ≫ g))

end Epi

end CategoryTheory.FilteredObject.Hom
