module

public import ReasLib.CategoryTheory.Sites.QuasiCompact.TestSet
public import stacks_project.Chap96.Definition_96_4_1_AssociatedTopology
public import stacks_project.Chap96.Definition_96_26_1_Affine
public import stacks_project.Chap100.Definition_100_6_1_QuasiCompact
public import stacks_project.Chap101.Definition_101_8_1_Noetherian

/-!
# Quasi-compact test sets on the associated fppf site

On a quasi-compact and quasi-separated algebraic stack, the affine objects of
`X_fppf` form a refining basis, so the associated fppf topology admits a
quasi-compact test set.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupoidsOver
open CategoryTheory.GrothendieckTopology.QuasiCompact
open CategoryTheory.GrothendieckTopology.QuasiCompact.TestSet

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Type-valued weak sheafification exists on the associated fppf topology of a
category fibred in groupoids. -/
instance fppfTopology.instHasWeakSheafify_type {S : Scheme.{u}}
    (X : GroupoidsOver S) :
    HasWeakSheafify X.fppfTopology (Type (u + 1)) :=
  sorry

/-- On a quasi-compact and quasi-separated algebraic stack, the affine objects of
the associated fppf site form a refining basis in the sense of Remark 7.17.9 (2). -/
instance affineObjects.instRefiningBasis {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsQuasiCompact X] [IsQuasiSeparated X] :
    RefiningBasis X.fppfTopology (affineObjects X) :=
  sorry

/-- A quasi-compact and quasi-separated algebraic stack has a quasi-compact test
set on its associated fppf topology. -/
instance fppfTopology.instHasTestSet {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsQuasiCompact X] [IsQuasiSeparated X] :
    HasTestSet X.fppfTopology :=
  sorry

end AlgebraicGeometry.AlgebraicStack
