/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Symmetry.Swap
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Equivalence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Swap equivalences for full-subbicategory two-fibre products

The ordinary explicit pseudo-pullback swap equivalence is lifted through the generic
full-subbicategory equivalence constructor. No unit, counit, or triangle data are rebuilt here.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

universe u v w vB

namespace CategoryTheory

open BasedCategory Bicategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace TwoFibreProduct

variable
  {P : ObjectProperty
    (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
variable [BasedCategory.PseudoPullback.ObjectProperty.IsClosedUnder P]
variable {X Y S : P.FullSubbicategory}

/-- The canonical equivalence exchanging the two entries of a full-subbicategory
two-fibre product. All coherence data are inherited from the ordinary swap equivalence. -/
@[stacks 0040 "swap equivalence of full-subbicategory two-fibre products"]
noncomputable def swap.equivalence (F : X ⟶ S) (G : Y ⟶ S) :
    apex F G ≌ apex G F :=
  ObjectProperty.FullSubbicategory.equivalenceOfAmbient
    (PseudoPullback.swap.equivalence F.hom G.hom)

/-- The forward morphism of the selected swap equivalence is the selected swap. -/
@[simp]
theorem swap.equivalence.hom (F : X ⟶ S) (G : Y ⟶ S) :
    (swap.equivalence F G).hom = swap F G := sorry

/-- The inverse morphism of the selected swap equivalence is the reverse selected swap. -/
@[simp]
theorem swap.equivalence.inv (F : X ⟶ S) (G : Y ⟶ S) :
    (swap.equivalence F G).inv = swap G F := sorry

/- Data audit: `swap.equivalence` changes only the bicategorical owner through
`ObjectProperty.FullSubbicategory.equivalenceOfAmbient`. Its inverse, unit, counit, and
coherence are the data of `PseudoPullback.swap.equivalence`; the generic
`equivalenceOfAmbient.*` API exposes them. -/

end TwoFibreProduct

end CategoryTheory
