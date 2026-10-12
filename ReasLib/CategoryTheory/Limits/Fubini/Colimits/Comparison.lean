/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Limits.Fubini.Colimits.Basic

/-!
# Canonical colimit Fubini comparisons

This leaf owns the canonical isomorphism from an iterated colimit to the total colimit and the
canonical isomorphism between the two orders of iteration.  Component formulas are isolated in
`Colimits.Computations`.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Limits

open CategoryTheory Functor

variable {I : Type u₁} [Category.{v₁} I]
variable {J : Type u₂} [Category.{v₂} J]
variable {C : Type u₃} [Category.{v₃} C]

namespace DiagramOfCocones

variable (M : I × J ⥤ C)

/-- Whenever both colimits exist, the colimit of the rowwise-colimit functor is canonically
isomorphic to the colimit of `M`. -/
@[stacks 002M "canonical identification of iterated and total colimit"]
noncomputable def colimitIso (D : DiagramOfCocones (curry.obj M))
    (hD : ∀ i, IsColimit (D.obj i)) [HasColimit D.coconePoints] [HasColimit M] :
    colimit D.coconePoints ≅ colimit M :=
  IsColimit.coconePointUniqueUpToIso
    ((colimit.isColimit D.coconePoints).totalCurry D hD)
    (colimit.isColimit M)

/-- Provided the total colimit and both indicated iterated colimits exist, the two orders of
iterated colimit are canonically isomorphic. -/
@[stacks 002M "canonical identification of the two iterated colimit orders"]
noncomputable def swapIso (D : DiagramOfCocones (curry.obj M))
    (hD : ∀ i, IsColimit (D.obj i))
    (E : DiagramOfCocones (curry.obj (Prod.swap J I ⋙ M)))
    (hE : ∀ j, IsColimit (E.obj j)) [HasColimit D.coconePoints]
    [HasColimit E.coconePoints] [HasColimit M] :
    colimit D.coconePoints ≅ colimit E.coconePoints :=
  IsColimit.coconePointsIsoOfEquivalence
    (s := D.curryTotalFunctor.obj (colimit.cocone D.coconePoints))
    (t := E.curryTotalFunctor.obj (colimit.cocone E.coconePoints))
    ((colimit.isColimit D.coconePoints).totalCurry D hD)
    ((colimit.isColimit E.coconePoints).totalCurry E hE)
    (Prod.braiding I J) (Iso.refl _)

end DiagramOfCocones

end CategoryTheory.Limits
