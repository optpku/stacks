/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

-- The reusable fixed-target factorization comparison is owned by the neutral module below.
-- This file retains only the source labels and their source-facing statements.
public import ReasLib.CategoryTheory.Fibered.Groupoids.Factorization
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

open scoped Bicategory

universe u v uX

namespace FiberedCategoryOver.Groupoids.Factorization

variable {C : Type u} [Category.{v} C]
variable {X X' X'' Y :
  FiberedCategoryOver.Groupoids.{u, v, max uX (max u v), v} C}
variable {F : X ⟶ Y} {f : X' ⟶ Y} {g : X'' ⟶ Y}
variable [Functor.IsFibered.InGroupoids (toFunctor f)]
variable [Functor.IsFibered.InGroupoids (toFunctor g)]
variable (a : X ≌ X') (b : X ≌ X'')
variable (ha_comm : Nonempty (a.hom ≫ f ≅ F))
variable (hb_comm : Nonempty (b.hom ≫ g ≅ F))

/- Lemma 4.35.17 (1): two `2`-commutative factorizations through functors fibred in groupoids,
whose source maps are bicategorical equivalences over the base, have bicategorically equivalent
intermediate categories over the target. The canonical statement also records the comparison
after forgetting to the base. -/
@[stacks 06N8 "(1)"]
#check (existsComparison.{u, v, uX} a b ha_comm hb_comm :
  ∃ e : BasedCategory.ofFunctor (toFunctor g) ≌
      BasedCategory.ofFunctor (toFunctor f),
    Nonempty
      (BasedFunctor.comp (toBasedFunctor b.hom)
          (BasedFunctor.forgetTarget e.hom) ≅
        toBasedFunctor a.hom))

variable (ha_strict : a.hom ≫ f = F) (hb_strict : b.hom ≫ g = F)

/- Lemma 4.35.17 (2): when both factorization triangles commute strictly, the comparison can be
chosen over the target itself. -/
@[stacks 06N8 "(2)"]
#check (existsStrictComparison.{u, v, uX} a b ha_strict hb_strict :
  ∃ e : BasedCategory.ofFunctor (toFunctor g) ≌
      BasedCategory.ofFunctor (toFunctor f),
    Nonempty
      (BasedFunctor.comp
          (BasedFunctor.Factorization.overTarget
            (toBasedFunctor b.hom) (congrArg toBasedFunctor hb_strict))
          e.hom ≅
        BasedFunctor.Factorization.overTarget
          (toBasedFunctor a.hom) (congrArg toBasedFunctor ha_strict)))

end FiberedCategoryOver.Groupoids.Factorization

end CategoryTheory
