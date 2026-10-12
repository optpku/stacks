/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Limits.Fubini.Limits.Basic

/-!
# Canonical limit Fubini comparisons

This leaf owns the canonical isomorphism from an iterated limit to the total limit and the
canonical isomorphism between the two orders of iteration.  Component formulas are isolated in
`Limits.Computations`.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Limits

open CategoryTheory Functor

variable {I : Type u₁} [Category.{v₁} I]
variable {J : Type u₂} [Category.{v₂} J]
variable {C : Type u₃} [Category.{v₃} C]

namespace DiagramOfCones

variable (M : I × J ⥤ C)

/-- Whenever both limits exist, the limit of the rowwise-limit functor is canonically isomorphic
to the limit of `M`. -/
@[stacks 002M "canonical identification of iterated and total limit"]
noncomputable def limitIso (D : DiagramOfCones (curry.obj M))
    (hD : ∀ i, IsLimit (D.obj i)) [HasLimit D.conePoints] [HasLimit M] :
    limit D.conePoints ≅ limit M :=
  IsLimit.conePointUniqueUpToIso
    ((limit.isLimit D.conePoints).totalCurry D hD)
    (limit.isLimit M)

/-- Provided the total limit and both indicated iterated limits exist, the two orders of
iterated limit are canonically isomorphic. -/
@[stacks 002M "canonical identification of the two iterated limit orders"]
noncomputable def swapIso (D : DiagramOfCones (curry.obj M))
    (hD : ∀ i, IsLimit (D.obj i))
    (E : DiagramOfCones (curry.obj (Prod.swap J I ⋙ M)))
    (hE : ∀ j, IsLimit (E.obj j)) [HasLimit D.conePoints]
    [HasLimit E.conePoints] [HasLimit M] : limit D.conePoints ≅ limit E.conePoints :=
  IsLimit.conePointsIsoOfEquivalence
    (s := D.curryTotalFunctor.obj (limit.cone D.conePoints))
    (t := E.curryTotalFunctor.obj (limit.cone E.conePoints))
    ((limit.isLimit D.conePoints).totalCurry D hD)
    ((limit.isLimit E.conePoints).totalCurry E hE)
    (Prod.braiding I J) (Iso.refl _)

end DiagramOfCones

end CategoryTheory.Limits
