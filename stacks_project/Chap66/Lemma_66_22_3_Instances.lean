/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.Ring.Sheaf.LocallyRinged
public import stacks_project.Chap66.Lemma_66_18_8_Topos
public import stacks_project.Chap66.Lemma_66_29_7_CommSheaf

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The universe-lifted commutative structure sheaf on the small étale site of an algebraic
space is locally ringed in the sense of `Sheaf.IsLocallyRinged`. -/
instance commStructureSheafLift_isLocallyRinged {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (commStructureSheafLift X).IsLocallyRinged := sorry

/-- Locally ringedness of `commStructureSheafLift X` unpacks as local nontriviality together
with local unit dichotomy. -/
theorem commStructureSheafLift_isLocallyRinged_iff {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (commStructureSheafLift X).IsLocallyRinged ↔
      IsIso (Sheaf.nontrivialityMap (commStructureSheafLift X)) ∧
        Sheaf.LocalUnitDichotomy (commStructureSheafLift X) := sorry

end AlgebraicGeometry.AlgebraicSpace
