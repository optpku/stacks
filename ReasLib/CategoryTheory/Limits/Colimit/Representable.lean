/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Representable functors and colimit comparisons

This leaf records the pointwise API for the canonical comparison
`colimit.post B (coyoneda.obj (op A))`.  The comparison itself remains Mathlib's owner;
the results here expose its stage computation and two reusable criteria for its underlying
function.
-/

@[expose] public section

open CategoryTheory Opposite

universe v u

namespace CategoryTheory.Limits

variable {J : Type v} [SmallCategory J]
variable {C : Type u} [Category.{v} C]

/-- On a stage representative, the representable colimit comparison is composition with the
corresponding colimit coprojection. -/
@[stacks 05NN "stage computation"]
theorem colimit_post_coyoneda_ι_app (A : C) (B : J ⥤ C) [HasColimit B] (j : J)
    (φ : A ⟶ B.obj j) :
    (colimit.ι (B ⋙ coyoneda.obj (op A)) j ≫ colimit.post B (coyoneda.obj (op A))) φ =
      φ ≫ colimit.ι B j := sorry

/-- If `Hom(A, -)` preserves a chosen colimit, its canonical comparison map is bijective. -/
theorem colimitPost_bijective_of_preserves (A : C) (B : J ⥤ C) [HasColimit B]
    [PreservesColimit B (coyoneda.obj (op A))] :
    Function.Bijective (colimit.post B (coyoneda.obj (op A))) := sorry

/-- For a filtered diagram whose coprojections are monomorphisms, the canonical comparison from
the colimit of `Hom(A, -)` is injective. -/
theorem colimitPost_injective_of_ι_mono [IsFiltered J] (A : C) (B : J ⥤ C)
    [HasColimit B] (hι : ∀ j : J, Mono (colimit.ι B j)) :
    Function.Injective (colimit.post B (coyoneda.obj (op A))) := sorry

end CategoryTheory.Limits
