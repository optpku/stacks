module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Projections
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Basic

@[expose] public section

open CategoryTheory
open scoped Bicategory BasedFunctor

universe u v w vB

namespace CategoryTheory

namespace BasedCategory

variable {C : Type u} [Category.{v} C]

namespace PseudoPullback
/-- The canonical `2`-commutative square in `Cat/C` whose apex is the explicit based
pseudo-pullback, whose legs are its two projections, and whose comparison is the stored
isomorphism. -/
@[stacks 0040 "canonical bilimit cone of an explicit based pseudo-pullback"]
noncomputable def cone
    {X Y S : BasedCategory.{max v vB, max w (max u (max v vB))} C}
    (F : X ⟶ S) (G : Y ⟶ S) :
    Bicategory.PseudoPullbackCone F G where
  pt := PseudoPullback F G
  fst := PseudoPullback.fst F G
  snd := PseudoPullback.snd F G
  iso := PseudoPullback.comparisonIso F G

/-- The apex of the canonical based pseudo-pullback cone is the explicit pseudo-pullback
owner. -/
@[simp]
theorem cone.pt
    {X Y S : BasedCategory.{max v vB, max w (max u (max v vB))} C}
    (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).pt = PseudoPullback F G := sorry

/-- The first leg of the canonical based pseudo-pullback cone is the explicit first
projection. -/
@[simp]
theorem cone.fst
    {X Y S : BasedCategory.{max v vB, max w (max u (max v vB))} C}
    (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).fst = PseudoPullback.fst F G := sorry

/-- The second leg of the canonical based pseudo-pullback cone is the explicit second
projection. -/
@[simp]
theorem cone.snd
    {X Y S : BasedCategory.{max v vB, max w (max u (max v vB))} C}
    (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).snd = PseudoPullback.snd F G := sorry

/-- The structural cell of the canonical based pseudo-pullback cone is the explicit comparison
isomorphism. -/
@[simp]
theorem cone.iso
    {X Y S : BasedCategory.{max v vB, max w (max u (max v vB))} C}
    (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).iso = PseudoPullback.comparisonIso F G := sorry

/-- The canonical square of the explicit based pseudo-pullback is a bicategorical
pseudo-pullback bilimit. -/
@[stacks 0040]
instance cone.isBilimit
    {X Y S : BasedCategory.{max v vB, max w (max u (max v vB))} C}
    (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).IsBilimit := sorry
/- Proof strategy: for every pseudo-pullback cone, construct the terminal factorization through
`cone F G` objectwise from its common base object, two legs, and comparison isomorphism. Use the
two leg comparisons to construct the unique based natural transformation between factorizations;
`PseudoPullback.hom_ext` proves uniqueness componentwise. -/

/- Data audit: `#print axioms CategoryTheory.BasedCategory.PseudoPullback.cone` reports
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`; the definition above fixes all four
non-Prop fields to the explicit existing owners, so `sorryAx` enters only through their inherited
proof-law fields. -/
end PseudoPullback
end BasedCategory
end CategoryTheory
