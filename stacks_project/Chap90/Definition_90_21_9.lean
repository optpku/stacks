/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Definition_90_21_9_Quotient
import StacksCheckRecall

universe u v w

open CategoryTheory

/- Definition 90.21.9 (1): for a groupoid in functors `G = (U, R, s, t, c)` on a
category `C`, the assignment `T ↦ (U(T), R(T), s, t, c)` is `G.toFunctor : C ⥤ Grpd`,
and the quotient category cofibered in groupoids `[U/R] ⟶ C` is
`GroupoidInFunctors.quotient G`, the category cofibered in groupoids associated to
this functor as in Remarks 90.5.2 (9). -/
@[stacks 06KB] #check GroupoidInFunctors.quotient

/- Definition 90.21.9 (2): the quotient morphism `U ⟶ [U/R]` is
`GroupoidInFunctors.quotientMorphism G`, the morphism of categories cofibered in
groupoids over `C` sending `x ∈ U(T)` to the object `(T, x)` and sending
`f : T ⟶ T'` to the Grothendieck morphism `(f, id) : (T, x) ⟶ (T', U(f)(x))`
lying over `f`. -/
@[stacks 06KB] #check GroupoidInFunctors.quotientMorphism
