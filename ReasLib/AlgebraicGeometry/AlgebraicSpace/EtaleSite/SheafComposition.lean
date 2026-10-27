/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Sites.Whiskering
public import ReasLib.Algebra.Category.CommRingCat.ULift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StructureSheaf.CommRing

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Sheaf CategoryTheory.Functor
open CategoryTheory.MonoidalCategory
open CategoryTheory.Abelian

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Universe lifting of commutative-ring sheaves exists on the small étale site. -/
instance smallEtaleTopology_hasSheafCompose_universeLift {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    (smallEtaleTopology X).HasSheafCompose CommRingCat.universeLift.{u, u + 1} :=
  sorry

/-- Commutative-ring-valued sheaf composition exists in universe `u + 1` on the
small étale topology of an algebraic space. -/
instance smallEtaleTopology_hasSheafCompose_commRing_succ {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    (smallEtaleTopology X).HasSheafCompose
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
  sorry

/-- Forgetting commutative rings to types exists in universe `u + 1` on the small
étale topology of an algebraic space. -/
instance smallEtaleTopology_hasSheafCompose_forget_commRing_succ {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    (smallEtaleTopology X).HasSheafCompose
      (CategoryTheory.forget CommRingCat.{u + 1}) :=
  sorry

/-- Forgetting commutative rings to types exists on the small étale topology of
an algebraic space. -/
instance smallEtaleTopology_hasSheafCompose_forget_commRing {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    (smallEtaleTopology X).HasSheafCompose
      (CategoryTheory.forget CommRingCat.{u}) :=
  sorry

/-- Universe lifting of abelian-group sheaves exists on the small étale site. -/
instance smallEtaleTopology_hasSheafCompose_addCommGrp_ulift {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    (smallEtaleTopology X).HasSheafCompose AddCommGrpCat.uliftFunctor.{u + 1, u} :=
  sorry

/-- Forgetting commutative rings to abelian groups exists on the small étale site. -/
instance smallEtaleTopology_hasSheafCompose_forgetAdd {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    (smallEtaleTopology X).HasSheafCompose
      (forget₂ CommRingCat.{u} RingCat.{u} ⋙
        forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  sorry

/-- Forgetting commutative rings to abelian groups exists in universe `u + 1` on
the small étale site. -/
instance smallEtaleTopology_hasSheafCompose_forgetAdd_succ {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    (smallEtaleTopology X).HasSheafCompose
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) :=
  sorry

/-- Identifying the universe lift of `𝒪_X` obtained by sheaf composition with the
canonical lifted structure sheaf. -/
def commStructureSheafComposeLiftIso {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (sheafCompose (smallEtaleTopology X)
        CommRingCat.universeLift.{u, u + 1}).obj (commStructureSheaf X) ≅
      commStructureSheafLift X :=
  (fullyFaithfulSheafToPresheaf (smallEtaleTopology X) CommRingCat.{u + 1}).preimageIso
    (Iso.refl _)

end AlgebraicGeometry.AlgebraicSpace
