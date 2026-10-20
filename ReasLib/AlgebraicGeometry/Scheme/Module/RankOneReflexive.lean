/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Monoidal.Skeleton
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.LocallyFree
public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive.Normal
public import ReasLib.RingTheory.Flatness.LocallyFree
import Mathlib.Tactic.CrossRefAttribute

/-!
# Rank-one reflexive modules

This file defines rank-one reflexive module sheaves and the type of their isomorphism classes.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]

/-- A module has rank one at the generic point when its generic stalk is finite locally free of
rank `1` over the generic local ring. -/
abbrev isRankOneAtGenericPoint (ℱ : X.Modules) : Prop :=
  Module.FiniteLocallyFreeOfRank (X.presheaf.stalk (genericPoint X))
    (RingedSpace.stalkModuleCat ℱ (genericPoint X)) 1

/-- A coherent module is rank-one reflexive when it is reflexive and has rank one at the generic
point. -/
@[stacks 0EBM]
class IsRankOneReflexive (ℱ : X.Modules) [ℱ.IsCoherent] : Prop where
  /-- The coherent module is reflexive. -/
  isReflexive : IsReflexive ℱ
  /-- The generic stalk of the coherent module has rank one. -/
  isRankOneAtGenericPoint : isRankOneAtGenericPoint X ℱ

/-- A rank-one reflexive coherent module is reflexive. -/
@[stacks 0EBM, instance]
instance instIsReflexiveOfIsRankOneReflexive (ℱ : X.Modules) [ℱ.IsCoherent]
    [hℱ : IsRankOneReflexive X ℱ] :
    IsReflexive ℱ :=
  hℱ.isReflexive

/-- A rank-one reflexive coherent module has rank one at the generic point. -/
@[stacks 0EBM, instance]
instance instIsRankOneAtGenericPointOfIsRankOneReflexive
    (ℱ : X.Modules) [ℱ.IsCoherent] [hℱ : IsRankOneReflexive X ℱ] :
    isRankOneAtGenericPoint X ℱ :=
  hℱ.isRankOneAtGenericPoint

/-- The defining conditions for a rank-one reflexive coherent module. -/
@[stacks 0EBM]
theorem isRankOneReflexive_iff (ℱ : X.Modules) [ℱ.IsCoherent] :
    IsRankOneReflexive X ℱ ↔
      IsReflexive ℱ ∧ isRankOneAtGenericPoint X ℱ := sorry

/-- On an integral locally Noetherian normal scheme, a rank-one reflexive coherent module is
finite locally free of rank one away from a closed subset whose irreducible components have
codimension at least two. -/
theorem exists_codimTwo_open_isFiniteLocallyFreeOfRank_one
    (hXnormal : X.isNormal) (ℱ : X.Modules) [ℱ.IsCoherent] [IsRankOneReflexive X ℱ] :
    ∃ U : X.Opens,
      Scheme.IdealSheafData.irreducibleComponentsCodimAtLeast 2 ((U : Set X)ᶜ : Set X) ∧
        SheafOfModules.IsFiniteLocallyFreeOfRank 1 ((Scheme.Modules.pullback U.ι).obj ℱ) := sorry

/-- The object property selecting rank-one coherent reflexive objects of `X.Modules`. -/
abbrev rankOneReflexiveModuleProperty : ObjectProperty X.Modules :=
  fun ℱ ↦ ∃ hℱ : ℱ.IsCoherent, @IsRankOneReflexive X _ ℱ hℱ

/-- The full subcategory of rank-one coherent reflexive objects of `X.Modules`. -/
abbrev RankOneReflexiveModule :=
  (rankOneReflexiveModuleProperty X).FullSubcategory

/-- The skeleton representing isomorphism classes of rank-one coherent reflexive objects of
`X.Modules`. -/
@[stacks 0EBL]
abbrev RankOneReflexiveIsoClass :=
  Skeleton (RankOneReflexiveModule X)

variable {X}

/-- The isomorphism class represented by a rank-one coherent reflexive object of `X.Modules`. -/
noncomputable def rankOneReflexiveIsoClassOf
    (ℱ : X.Modules) [ℱ.IsCoherent] [IsRankOneReflexive X ℱ] : RankOneReflexiveIsoClass X :=
  toSkeleton (⟨ℱ, ⟨inferInstance, inferInstance⟩⟩ : RankOneReflexiveModule X)

end AlgebraicGeometry.Scheme.Modules
