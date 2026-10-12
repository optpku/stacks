/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.Colimit.Representable
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits Opposite

universe v u

variable {J : Type v} [SmallCategory J]
variable {C : Type u} [Category.{v} C]
variable (A : C) (B : J ⥤ C) [HasColimit B]

/- 19.2.0.1 (05NN): the comparison
`colim_j Hom(A, B.obj j) → Hom(A, colim_j B.obj j)` is Mathlib's canonical `colimit.post`. -/
@[stacks 05NN] #check
  (colimit.post B (coyoneda.obj (op A)) :
    colimit (B ⋙ coyoneda.obj (op A)) ⟶ (A ⟶ colimit B))

/- The reusable stage computation for the comparison map. -/
#check @CategoryTheory.Limits.colimit_post_coyoneda_ι_app
