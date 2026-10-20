/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Picard

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Example 33.30.4: if `t` is a closed point of the projective line over a field and `U` is its
complement, then `Pic(U)` is additively equivalent to `ZMod` of the residue degree of `t`. -/
@[stacks 0CDP] #check
  (AlgebraicGeometry.ProjectiveSpace.nonempty_picardGroup_puncturedLine_equiv_zmod_residueDegree :
    ∀ (k : Type u) [Field k]
      (t : ProjectiveSpace.scheme k 1) (ht : t ∈ closedPoints (ProjectiveSpace.scheme k 1))
      (U : (ProjectiveSpace.scheme k 1).Opens)
      (hU : (U : Set (ProjectiveSpace.scheme k 1)) =
        ({t} : Set (ProjectiveSpace.scheme k 1))ᶜ),
      Nonempty
        (U.toScheme.PicardGroup ≃+
          ZMod ((ProjectiveSpace.toSpec k 1).residueDegree t)))

/- Restriction to the punctured projective line is surjective on Picard groups. -/
#check
  (AlgebraicGeometry.ProjectiveSpace.picardPullback_surjective_puncturedLine :
    ∀ (k : Type u) [Field k]
      (t : ProjectiveSpace.scheme k 1) (ht : t ∈ closedPoints (ProjectiveSpace.scheme k 1))
      (U : (ProjectiveSpace.scheme k 1).Opens)
      (hU : (U : Set (ProjectiveSpace.scheme k 1)) =
        ({t} : Set (ProjectiveSpace.scheme k 1))ᶜ),
      Function.Surjective (Scheme.Hom.picardPullback U.ι))

/- The punctured projective line has nontrivial Picard group when the removed point is not
rational over the base field. -/
#check
  (AlgebraicGeometry.ProjectiveSpace.nontrivial_picardGroup_puncturedLine_of_not_rational :
    ∀ (k : Type u) [Field k]
      (t : ProjectiveSpace.scheme k 1) (ht : t ∈ closedPoints (ProjectiveSpace.scheme k 1))
      (U : (ProjectiveSpace.scheme k 1).Opens)
      (hU : (U : Set (ProjectiveSpace.scheme k 1)) =
        ({t} : Set (ProjectiveSpace.scheme k 1))ᶜ),
      ¬ IsIso ((ProjectiveSpace.toSpec k 1).residueFieldMap t) →
        Nontrivial U.toScheme.PicardGroup)

/- A compatible embedding of the removed point's residue field into a field extension makes
the Picard group of the base-changed punctured projective line trivial. -/
#check
  (AlgebraicGeometry.ProjectiveSpace.subsingleton_picardGroup_puncturedLine_baseChange :
    ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k']
      (t : ProjectiveSpace.scheme k 1) (ht : t ∈ closedPoints (ProjectiveSpace.scheme k 1))
      (U : (ProjectiveSpace.scheme k 1).Opens)
      (hU : (U : Set (ProjectiveSpace.scheme k 1)) =
        ({t} : Set (ProjectiveSpace.scheme k 1))ᶜ)
      (ι : (ProjectiveSpace.scheme k 1).residueField t →+* k')
      (hι : ι.comp
          (Scheme.Hom.ResidueField.mapOfSpec (ProjectiveSpace.toSpec k 1) t) =
        algebraMap k k'),
      Subsingleton
        (FieldExtension.baseChange k k' (U.ι ≫ ProjectiveSpace.toSpec k 1)).PicardGroup)
