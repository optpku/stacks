/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap98.Definition_98_13_1_Versal
import StacksCheckRecall

@[expose] public section

/- Definition 98.12.2
Let S be a locally Noetherian scheme. Let 𝒳 be fibred in groupoids over
(Sch/S)_fppf. Let U be a scheme locally of finite type over S. Let x be an
object of 𝒳 lying over U. Let u0 be a finite type point of U. We say x is
versal at u0 if the morphism hat x of predeformation categories from
98.12.1.1 is smooth in the sense of BasedFunctor.IsSmooth
(Definition 90.8.1). -/
@[stacks 07XF] #check AlgebraicGeometry.GroupoidsOver.IsVersalAt
