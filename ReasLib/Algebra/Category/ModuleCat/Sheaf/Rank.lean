/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.LinearAlgebra.Dimension.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stalk ranks of sheaves of modules

The rank of a module-sheaf stalk is canonical for any sheaf of commutative rings on a
topological space. Local freeness supplies the locally constant specification, while finite
local freeness of fixed rank identifies the function with a constant natural-valued rank.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace SheafOfModules

variable {X : TopCat.{u}} {𝒪 : X.Sheaf CommRingCat.{u}}

/-- The extended-natural rank of the stalk of a sheaf of modules. -/
@[stacks 01C9 "canonical stalk-rank function"]
noncomputable def rankAtStalk
    (F : SheafOfModules.{u} (TopCat.Sheaf.ringSheafOfComm 𝒪)) (x : X) : ℕ∞ :=
  Cardinal.toENat
    (Module.rank (𝒪.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x))

/-- The canonical stalk-rank function is invariant under isomorphism of module sheaves. -/
@[stacks 01C9 "stalk-rank invariance under isomorphism"]
theorem rankAtStalk_eq_of_iso
    {F G : SheafOfModules.{u} (TopCat.Sheaf.ringSheafOfComm 𝒪)} (e : F ≅ G) :
    rankAtStalk F = rankAtStalk G := sorry

/-- The stalk rank is the cardinality of any basis identifying the stalk with a standard free
module. -/
theorem rankAtStalk_eq_card_of_iso
    (F : SheafOfModules.{u} (TopCat.Sheaf.ringSheafOfComm 𝒪)) {x : X}
    [Nontrivial (𝒪.presheaf.stalk x)] (I : Type u)
    (e : (stalkFunctorOfCommRing 𝒪 x).obj F ≅
      (ModuleCat.free (𝒪.presheaf.stalk x)).obj I) :
    rankAtStalk F x = ENat.card I := sorry

/-- A function is a rank function for `F` when it is locally constant and records the
cardinality of every local free basis. -/
@[stacks 01C9 "rank-function specification"]
def IsRankFunction
    (F : SheafOfModules.{u} (TopCat.Sheaf.ringSheafOfComm 𝒪))
    (rank : X → ℕ∞) : Prop :=
  IsLocallyConstant rank ∧
    ∀ (x : X) (U : Opens X) (_ : x ∈ U) (I : Type u),
      Nonempty
          (F.over U ≅
            (SheafOfModules.free.{u} I :
              SheafOfModules.{u}
                ((TopCat.Sheaf.ringSheafOfComm 𝒪).over U))) →
        rank x = ENat.card I

/-- The two defining clauses of a locally free rank function. -/
@[stacks 01C9 "rank-function specification iff"]
theorem isRankFunction_iff
    (F : SheafOfModules.{u} (TopCat.Sheaf.ringSheafOfComm 𝒪))
    (rank : X → ℕ∞) :
    IsRankFunction F rank ↔
      IsLocallyConstant rank ∧
        ∀ (x : X) (U : Opens X) (_ : x ∈ U) (I : Type u),
          Nonempty
              (F.over U ≅
                (SheafOfModules.free.{u} I :
                  SheafOfModules.{u}
                    ((TopCat.Sheaf.ringSheafOfComm 𝒪).over U))) →
            rank x = ENat.card I := sorry

namespace IsRankFunction

/-- A rank function of a locally free module sheaf is locally constant. -/
theorem isLocallyConstant
    {F : SheafOfModules.{u} (TopCat.Sheaf.ringSheafOfComm 𝒪)}
    {rank : X → ℕ∞} (h : IsRankFunction F rank) :
    IsLocallyConstant rank := sorry

/-- A rank function evaluates to the cardinality of any local free basis through the point. -/
theorem eq_card
    {F : SheafOfModules.{u} (TopCat.Sheaf.ringSheafOfComm 𝒪)}
    {rank : X → ℕ∞} (h : IsRankFunction F rank)
    (x : X) (U : Opens X) (hx : x ∈ U) (I : Type u)
    (e : Nonempty
      (F.over U ≅
        (SheafOfModules.free.{u} I :
          SheafOfModules.{u} ((TopCat.Sheaf.ringSheafOfComm 𝒪).over U)))) :
    rank x = ENat.card I := sorry

/-- Rank functions satisfying the local free-basis specification are unique. -/
theorem eq
    {F : SheafOfModules.{u} (TopCat.Sheaf.ringSheafOfComm 𝒪)}
    [F.IsLocallyFree] {rank rank' : X → ℕ∞}
    (h : IsRankFunction F rank) (h' : IsRankFunction F rank') :
    rank = rank' := sorry

end IsRankFunction

namespace IsLocallyFree

/-- Lemma 17.14.4 (01C9): the canonical stalk-rank function of a locally free module sheaf
satisfies the locally constant free-basis specification when all coefficient-ring stalks are
nontrivial. -/
@[stacks 01C9 "canonical rank function"]
theorem rankAtStalk_isRankFunction
    (F : SheafOfModules.{u} (TopCat.Sheaf.ringSheafOfComm 𝒪)) [F.IsLocallyFree]
    (h𝒪 : ∀ x : X, Nontrivial (𝒪.presheaf.stalk x)) :
    IsRankFunction F (rankAtStalk F) := sorry

/-- The canonical stalk-rank function of a locally free module sheaf is locally constant. -/
@[stacks 01C9 "locally constant stalk rank"]
theorem rankAtStalk_isLocallyConstant
    (F : SheafOfModules.{u} (TopCat.Sheaf.ringSheafOfComm 𝒪)) [F.IsLocallyFree]
    (h𝒪 : ∀ x : X, Nontrivial (𝒪.presheaf.stalk x)) :
    IsLocallyConstant (rankAtStalk F) := sorry

/-- A locally free module sheaf over nontrivial stalk rings admits a rank function. -/
@[stacks 01C9 "existence of a rank function"]
theorem exists_rankFunction
    (F : SheafOfModules.{u} (TopCat.Sheaf.ringSheafOfComm 𝒪)) [F.IsLocallyFree]
    (h𝒪 : ∀ x : X, Nontrivial (𝒪.presheaf.stalk x)) :
    ∃ rank : X → ℕ∞, IsRankFunction F rank := sorry

/-- The locally free rank function over nontrivial stalk rings exists uniquely. -/
theorem existsUnique_rankFunction
    (F : SheafOfModules.{u} (TopCat.Sheaf.ringSheafOfComm 𝒪)) [F.IsLocallyFree]
    (h𝒪 : ∀ x : X, Nontrivial (𝒪.presheaf.stalk x)) :
    ∃! rank : X → ℕ∞, IsRankFunction F rank := sorry

end IsLocallyFree

namespace IsFiniteLocallyFreeOfRank

/-- A finite locally free module sheaf of rank `r` has constant canonical stalk rank `r` when
all coefficient-ring stalks are nontrivial. -/
@[stacks 01C9 "stalk rank of a fixed-rank module"]
theorem rankAtStalk_eq
    (r : ℕ) (F : SheafOfModules.{u} (TopCat.Sheaf.ringSheafOfComm 𝒪))
    [SheafOfModules.IsFiniteLocallyFreeOfRank
      (C := Opens X) (J := Opens.grothendieckTopology X)
      (R := TopCat.Sheaf.ringSheafOfComm 𝒪) r F]
    (h𝒪 : ∀ x : X, Nontrivial (𝒪.presheaf.stalk x)) :
    SheafOfModules.rankAtStalk F = fun _ ↦ (r : ℕ∞) := sorry

end IsFiniteLocallyFreeOfRank

end SheafOfModules
