/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.SquareZeroPullback
public import stacks_project.Chap90.Lemma_90_10_7_DualNumber
public import stacks_project.Chap90.«90_17_5_3_SquareZero»

/-!
# Square-zero pullbacks and their projections
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits ArtinianLocalAlgCat

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (A : ArtinianLocalAlgCat Λ k)
variable (I : Type u) [AddCommGroup I] [Module k I] [Module.Finite k I]

#check (ArtinianLocalAlgCat.squareZeroPullback A I : ArtinianLocalAlgCat Λ k)

#check (ArtinianLocalAlgCat.squareZeroPullbackFst A I : squareZeroPullback A I ⟶ A)

#check (ArtinianLocalAlgCat.squareZeroPullbackSnd A I :
  squareZeroPullback A I ⟶ squareZero Λ k I)

#check (ArtinianLocalAlgCat.squareZeroPullbackSection A I : A ⟶ squareZeroPullback A I)

#check (ArtinianLocalAlgCat.isPullback_squareZeroPullback A I :
  IsPullback (squareZeroPullbackFst A I) (squareZeroPullbackSnd A I)
    (toResidue A) (squareZeroToResidue Λ k I))

#check (ArtinianLocalAlgCat.squareZeroPullbackSection_comp_fst A I :
  squareZeroPullbackSection A I ≫ squareZeroPullbackFst A I = 𝟙 A)
