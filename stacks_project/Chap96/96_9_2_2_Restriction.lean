/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap96.Definition_96_4_1_AssociatedTopology
public import stacks_project.Chap96.«96_9_2_1_Restriction»

/-!
# Small-étale sheaf restriction along an object of a groupoid fibration

An étale sheaf on a category fibred in groupoids restricts along an object
`x` to a sheaf on the small étale site of `U = p(x)`, by packaging the
presheaf restriction `restrictSmallEtale`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X : GroupoidsOver S}

/-- Restriction of an étale sheaf on `X` to the small étale site of `U = p(x)`,
obtained by packaging `restrictSmallEtale x F.obj`. -/
def restrictSmallEtaleSheaf (F : Sheaf X.etaleTopology (Type (u + 1))) (x : X.total) :
    Sheaf (X.p.obj x).left.smallEtaleTopology (Type (u + 1)) where
  obj := restrictSmallEtale x F.obj
  property := sorry

/-- The underlying presheaf of `restrictSmallEtaleSheaf F x` is
`restrictSmallEtale x F.obj`. -/
theorem restrictSmallEtaleSheaf_obj (F : Sheaf X.etaleTopology (Type (u + 1)))
    (x : X.total) :
    (restrictSmallEtaleSheaf F x).obj = restrictSmallEtale x F.obj :=
  sorry

end AlgebraicGeometry.GroupoidsOver
