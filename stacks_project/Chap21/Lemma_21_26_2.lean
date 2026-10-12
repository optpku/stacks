/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.HomotopyCategory.QuasiIso.Triangle
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.26.2

The chapter entry is a direct recall of the reusable homotopy-category triangle API.  The
Mayer--Vietoris specialization imports this leaf rather than owning another copy of the
two-out-of-three argument.
-/

open CategoryTheory.Pretriangulated

@[stacks 0EWP]
#check @CategoryTheory.Pretriangulated.TriangleMorphism.quasiIso_two_out_of_three

#check @CategoryTheory.Pretriangulated.TriangleMorphism.quasiIso₃_of_quasiIso₁₂
#check @CategoryTheory.Pretriangulated.TriangleMorphism.quasiIso₂_of_quasiIso₁₃
#check @CategoryTheory.Pretriangulated.TriangleMorphism.quasiIso₁_of_quasiIso₂₃

end
