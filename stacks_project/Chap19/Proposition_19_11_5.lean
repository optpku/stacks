/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.MorphismProperty.OrdinalSmall.Grothendieck
import StacksCheckRecall

/-!
# Proposition 19.11.5

The reusable owner is
`MorphismProperty.IsOrdinalSmall.monomorphisms_of_cardinalMk_lt_cof`.
-/

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
  [IsGrothendieckAbelian.{max u v} C]

/- Proposition 19.11.5: if `Cardinal.mk (Subobject M) < α.cof`, then `M` is `α`-small
relative to monomorphisms. -/
@[stacks 079F] #check
  fun (M : C) (α : Ordinal.{max u v})
      (hM : Cardinal.mk (Subobject M) < α.cof) ↦
    (MorphismProperty.IsOrdinalSmall.monomorphisms_of_cardinalMk_lt_cof M α hM :
      (MorphismProperty.monomorphisms C).IsOrdinalSmall M α)
