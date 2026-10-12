/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Stage representatives for concrete colimits

When a `Type`-valued functor preserves a colimit, every underlying element of the colimit object
comes from an element at one of the diagram stages.  This is the concrete bridge behind many
filtered-colimit arguments in algebraic categories.
-/

@[expose] public section

open CategoryTheory

universe w vC uC vJ uJ

namespace CategoryTheory.Limits

variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C]

/-- Every underlying element of the point of a colimit cocone preserved by
`U : C ⥤ Type w` has a representative at one of the diagram stages. -/
theorem IsColimit.exists_ι_preimage (U : C ⥤ Type w) (B : J ⥤ C)
    {c : Cocone B} (hc : IsColimit c) [PreservesColimit B U]
    (x : U.obj c.pt) :
    ∃ (j : J) (y : U.obj (B.obj j)), U.map (c.ι.app j) y = x := sorry

/-- Every underlying element of a colimit preserved by `U : C ⥤ Type w` has a stage
representative. -/
theorem exists_colimit_ι_preimage (U : C ⥤ Type w) (B : J ⥤ C) [HasColimit B]
    [PreservesColimit B U] (x : U.obj (colimit B)) :
    ∃ (j : J) (y : U.obj (B.obj j)), U.map (colimit.ι B j) y = x := sorry

end CategoryTheory.Limits
