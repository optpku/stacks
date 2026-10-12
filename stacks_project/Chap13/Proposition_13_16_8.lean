/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.LeftDerived.Canonical
import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Canonical
import StacksCheckRecall

@[expose] public section

/-!
# Proposition 13.16.8 (05TA)

The proposition is a source-facing view of the reusable bounded acyclic-class API. The canonical
object properties are `Functor.RightAcyclic.Bounded` and `Functor.LeftAcyclic.Bounded`; the chapter
does not re-own their replacement or cone arguments.
-/

open CategoryTheory
open CategoryTheory.Functor

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  (F : A ⥤ B) [F.Additive]

section Right

variable [(Functor.RightAcyclic.Bounded F).HasMonoEmbedding]

/- Proposition 13.16.8 (05TA) (1): enough bounded-below right-acyclic objects make the
bounded-below right-derived functor source-defined everywhere. -/
@[stacks 05TA] #check
  (inferInstance :
    Functor.RightDerived.EverywhereDefined F.toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso A))

/- Proposition 13.16.8 (05TA) (2): the resulting total right-derived functor is exact, expressed
by the canonical triangulated-functor owner. -/
@[stacks 05TA] #check
  (inferInstance :
    (Functor.RightDerived.Bounded.functor F).IsTriangulated)

/- Proposition 13.16.8 (05TA) (3): every termwise bounded-below right-acyclic complex computes
the bounded-below right-derived functor. -/
@[stacks 05TA] #check
  @Functor.RightAcyclic.Bounded.computesAt_of_termwise

end Right

section Left

variable [(Functor.LeftAcyclic.Bounded F).HasEpiCover]

/- Proposition 13.16.8 (05TA) (4): enough bounded-above left-acyclic objects make the
bounded-above left-derived functor source-defined everywhere. -/
@[stacks 05TA] #check
  (inferInstance :
    Functor.LeftDerived.EverywhereDefined F.toBoundedAboveDerived
      (HomotopyCategory.Minus.quasiIso A))

/- Proposition 13.16.8 (05TA) (5): the resulting total left-derived functor is exact, expressed
by the canonical triangulated-functor owner. -/
@[stacks 05TA] #check
  (inferInstance :
    (Functor.LeftDerived.Bounded.functor F).IsTriangulated)

/- Proposition 13.16.8 (05TA) (6): every termwise bounded-above left-acyclic complex computes
the bounded-above left-derived functor. -/
@[stacks 05TA] #check
  @Functor.LeftAcyclic.Bounded.computesAt_of_termwise

end Left

end CategoryTheory
