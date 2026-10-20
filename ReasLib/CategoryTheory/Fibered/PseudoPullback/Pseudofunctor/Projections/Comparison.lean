module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Pseudofunctor.Construction.Action
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Projection
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projection comparisons for the explicit pseudo-pullback pseudofunctor

The first- and second-projection comparison isomorphisms and direct readouts of both cells.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open BasedFunctor
open BasedNatIso
open Functor.IsHomLift
open Functor.Fiber
open CategoricalPullback
open scoped CategoricalPullback
open scoped Bicategory BasedFunctor Pseudofunctor.StrongTrans

universe u v w vB

namespace CategoryTheory

open Bicategory

namespace BasedCategory

variable {C : Type u} [Category.{v} C]

namespace PseudoPullback

noncomputable section

/-- The first-projection comparison for the bundled pseudo-pullback action. -/
@[stacks 0040 "first projection comparison for the explicit pseudo-pullback pseudofunctor"]
def pseudofunctor.fstIso
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (ψ : S ⟶ T) :
    (pseudofunctor C).map ψ ⋙ fst T.fst T.snd ≅
      fst S.fst S.snd ⋙ Bicategory.Cospan.Hom.left ψ :=
  map.fstIso (Bicategory.Cospan.Hom.toBasedTransform ψ)

/-- The second-projection comparison for the bundled pseudo-pullback action. -/
@[stacks 0040 "second projection comparison for the explicit pseudo-pullback pseudofunctor"]
def pseudofunctor.sndIso
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (ψ : S ⟶ T) :
    (pseudofunctor C).map ψ ⋙ snd T.fst T.snd ≅
      snd S.fst S.snd ⋙ Bicategory.Cospan.Hom.right ψ :=
  map.sndIso (Bicategory.Cospan.Hom.toBasedTransform ψ)

/-- The forward first-projection comparison is the forward explicit comparison cell. -/
@[simp]
theorem pseudofunctor.fstIso.hom
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (ψ : S ⟶ T) :
    (pseudofunctor.fstIso ψ).hom =
      (map.fstIso (Bicategory.Cospan.Hom.toBasedTransform ψ)).hom := sorry

/-- The inverse first-projection comparison is the inverse explicit comparison cell. -/
@[simp]
theorem pseudofunctor.fstIso.inv
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (ψ : S ⟶ T) :
    (pseudofunctor.fstIso ψ).inv =
      (map.fstIso (Bicategory.Cospan.Hom.toBasedTransform ψ)).inv := sorry

/-- The forward second-projection comparison is the forward explicit comparison cell. -/
@[simp]
theorem pseudofunctor.sndIso.hom
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (ψ : S ⟶ T) :
    (pseudofunctor.sndIso ψ).hom =
      (map.sndIso (Bicategory.Cospan.Hom.toBasedTransform ψ)).hom := sorry

/-- The inverse second-projection comparison is the inverse explicit comparison cell. -/
@[simp]
theorem pseudofunctor.sndIso.inv
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (ψ : S ⟶ T) :
    (pseudofunctor.sndIso ψ).inv =
      (map.sndIso (Bicategory.Cospan.Hom.toBasedTransform ψ)).inv := sorry

end

end PseudoPullback

end BasedCategory

end CategoryTheory
