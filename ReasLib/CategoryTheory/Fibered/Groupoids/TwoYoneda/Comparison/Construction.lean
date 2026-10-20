/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.Groupoids.TwoYoneda.SplitModel

/-!
# Evaluation from the two-Yoneda split model

This file owns evaluation at the identity as a based functor from the split co-Grothendieck
model, together with its object, morphism, and projection computations. The raw functor assembly
remains private so downstream code depends only on stable computations.
-/

@[expose] public section

universe v u vS uS

namespace CategoryTheory

open scoped BasedFunctor

variable {C : Type u} [Category.{v} C]
variable {S : Type uS} [Category.{vS} S]

namespace TwoYoneda

section SplitToOriginalImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- Evaluation at the identity on objects of the split model: `(U, x) ↦ x(𝟙 U)`. -/
private def splitToOriginalObj (p : S ⥤ C) : splitCategory p → S :=
  fun X ↦
    ((X.2 : BasedCategory.Yoneda.hom p X.1)).obj (Over.mk (𝟙 X.1))

/-- Evaluation on a morphism `(f, η)` in the split model. It evaluates `η` at `𝟙 U` and then
applies the target based functor to `Over.mapIdentityToIdentity f`. -/
private def splitToOriginalMap (p : S ⥤ C)
    {X Y : splitCategory p} (φ : X ⟶ Y) :
    splitToOriginalObj p X ⟶ splitToOriginalObj p Y :=
  ((φ.2 :
      (X.2 : BasedCategory.Yoneda.hom p X.1) ⟶
        (TwoYoneda.map p φ.1).obj (Y.2 : BasedCategory.Yoneda.hom p Y.1)).app
          (Over.mk (𝟙 X.1))) ≫
    ((Y.2 : BasedCategory.Yoneda.hom p Y.1).map
      (Over.mapIdentityToIdentity φ.1))

/-- Evaluation on the identity co-Grothendieck morphism is the identity. -/
private theorem splitToOriginalMap_id (p : S ⥤ C) (X : splitCategory p) :
    splitToOriginalMap p (𝟙 X) = 𝟙 (splitToOriginalObj p X) := sorry
/- Proof strategy: expand the co-Grothendieck identity, cancel its `mapId` comparison, and
identify the tautological slice arrow over `𝟙 X.1` with the identity. -/

/-- Evaluation on co-Grothendieck morphisms respects composition. -/
private theorem splitToOriginalMap_comp (p : S ⥤ C)
    {X Y Z : splitCategory p} (f : X ⟶ Y) (g : Y ⟶ Z) :
    splitToOriginalMap p (f ≫ g) =
      splitToOriginalMap p f ≫ splitToOriginalMap p g := sorry
/- Proof strategy: use naturality of the second fiber component at the tautological slice arrow,
then the co-Grothendieck `mapComp` comparison and functoriality of the target based functor. -/

/-- The underlying evaluation functor from the split total category to `S`. Its object and map
payload are explicit; the two functor laws are the named theorems above. -/
private def splitToOriginalFunctor (p : S ⥤ C) : splitCategory p ⥤ S where
  obj := splitToOriginalObj p
  map := splitToOriginalMap p
  map_id := splitToOriginalMap_id p
  map_comp := splitToOriginalMap_comp p

/-- The evaluation functor commutes strictly with the projections to `C`. -/
private theorem splitToOriginalFunctor_comp_projection (p : S ⥤ C) :
    splitToOriginalFunctor p ⋙ p = (splitModel p).p := sorry
/- Proof strategy: use `Functor.ext`. On objects evaluate the based-functor projection equality
at `Over.mk (𝟙 U)`; on arrows the natural-transformation component is vertical and the
tautological slice arrow lies over the co-Grothendieck base arrow. -/

end Implementation

/-- The canonical based functor over `C` from the split 2-Yoneda model to the original category. -/
@[stacks 076J "2-Yoneda comparison to the original fibred category"]
def splitToOriginal (p : S ⥤ C) :
    splitModel p ⥤ᵇ BasedCategory.ofFunctor p where
  toFunctor := Implementation.splitToOriginalFunctor p
  w := Implementation.splitToOriginalFunctor_comp_projection p

end SplitToOriginalImplementation

namespace splitToOriginal

/-- Evaluation at the identity in the split model commutes strictly with the projections to the
base category. -/
@[simp]
theorem comm (p : S ⥤ C) :
    (splitToOriginal p).toFunctor ⋙ p = (splitModel p).p := sorry

/-- Evaluation at the identity computes the object map of the canonical comparison:
the split object `(U, x)` is sent to `x.obj (Over.mk (𝟙 U))`. -/
@[simp]
theorem obj (p : S ⥤ C) (X : splitCategory p) :
    (splitToOriginal p).toFunctor.obj X =
      ((X.2 : BasedCategory.Yoneda.hom p X.1)).obj (Over.mk (𝟙 X.1)) := sorry
/- Proof strategy: unfold the public comparison through its private implementation; its object
component is definitionally evaluation of the stored based functor at the identity slice. -/

/-- Evaluation at the identity computes the morphism map of the canonical comparison. It first
evaluates the stored natural transformation at `Over.mk (𝟙 X.1)`, then applies the target based
functor to the canonical slice arrow represented by `φ.1`. -/
@[simp]
theorem map (p : S ⥤ C)
    {X Y : splitCategory p} (φ : X ⟶ Y) :
    (splitToOriginal p).toFunctor.map φ =
      ((φ.2 :
          (X.2 : BasedCategory.Yoneda.hom p X.1) ⟶
            (TwoYoneda.map p φ.1).obj (Y.2 : BasedCategory.Yoneda.hom p Y.1)).app
            (Over.mk (𝟙 X.1))) ≫
        ((Y.2 : BasedCategory.Yoneda.hom p Y.1).map
          (Over.mapIdentityToIdentity φ.1)) := sorry
/- Proof strategy: unfold the public comparison through its private implementation. -/

end splitToOriginal

end TwoYoneda

end CategoryTheory
