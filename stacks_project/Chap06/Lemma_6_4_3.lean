/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.Lift.AddCommGrp.Operations
public import ReasLib.Topology.Sheaves.Abelian
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopCat
open scoped TopCat

universe u v

variable {X : TopCat.{u}} (F : X.Presheaf (Type v))

/-
The four textbook presentations are instances of generic operation presentations for a fixed
type-valued functor.  The neutral `CategoryTheory.Functor.Lift.AddCommGrp` API owns their
constructions and equivalences; this item records the specialization to the presheaf category.
-/

/- Lemma 6.4.3 (1): compatible sectionwise groups are naturally equivalent to `PAb(X)`-lifts of
the fixed presheaf `F`. -/
@[stacks 006J "sectionwise groups and additive restrictions"]
#check (CompatibleAddCommGroupStructure.equivAddCommGrpCatLift F :
  CompatibleAddCommGroupStructure F ≃
    { ℱ : PAb(X) // ℱ ⋙ forget AddCommGrpCat = F })

/- Lemma 6.4.3 (2): pointwise `0`, `-`, `+` axioms are naturally equivalent to `PAb(X)`-lifts of
the fixed presheaf `F`. -/
@[stacks 006J "presheaf operations satisfying the abelian-group axioms"]
#check (CompatibleAddCommGroupMaps.equivAddCommGrpCatLift F :
  CompatibleAddCommGroupMaps F ≃
    { ℱ : PAb(X) // ℱ ⋙ forget AddCommGrpCat = F })

/- Lemma 6.4.3 (3): presheaf operations with their sectionwise groups are naturally equivalent
to `PAb(X)`-lifts of the fixed presheaf `F`. -/
@[stacks 006J "presheaf operations defining the sectionwise abelian groups"]
#check (CompatibleAddCommGroupMapStructure.equivAddCommGrpCatLift F :
  CompatibleAddCommGroupMapStructure F ≃
    { ℱ : PAb(X) // ℱ ⋙ forget AddCommGrpCat = F })

/- Lemma 6.4.3 (4): an addition map defining sectionwise abelian groups is naturally equivalent
to `PAb(X)`-lifts of the fixed presheaf `F`. -/
@[stacks 006J "an addition map defining the sectionwise abelian groups"]
#check (CompatibleAdditionMapStructure.equivAddCommGrpCatLift F :
  CompatibleAdditionMapStructure F ≃
    { ℱ : PAb(X) // ℱ ⋙ forget AddCommGrpCat = F })
