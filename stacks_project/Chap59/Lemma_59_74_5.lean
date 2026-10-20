/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.Support.Ind
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace CategoryTheory.Sheaf

variable {X : Scheme.{u}} [IsNoetherian X]

/- Lemma 59.74.5 (1): on a Noetherian scheme `X`, if `E ⊆ X` is stable under specialization
and `F` is a torsion abelian étale sheaf with support contained in `E`, then `F` is a filtered
colimit of constructible abelian sheaves `G` whose supports lie in closed subsets of `E`. -/
@[stacks 0F0N] #check
  (CategoryTheory.Sheaf.isConstructibleEtaleAddCommGrp_ind_of_support :
    ∀ {X : Scheme.{u}} [IsNoetherian X]
      [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
      {E : Set X}, StableUnderSpecialization E →
      ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
        IsLocallyTorsion F → abelianSheafSupport F ⊆ E →
        ObjectProperty.ind.{u + 1}
          (fun G ↦ IsConstructibleEtaleAddCommGrp
            (fun {Y} f ↦
              ((Scheme.smallEtalePullback f).sheafPullback (AddCommGrpCat.{u + 1})
                X.smallEtaleTopology Y.smallEtaleTopology).obj)
            (fun {Y} G ↦ IsFiniteLocallyConstantAddCommGrp G) G ∧
            ∃ Z : Set X, IsClosed Z ∧ Z ⊆ E ∧ abelianSheafSupport G ⊆ Z) F)

/- Lemma 59.74.5 (2): on a Noetherian scheme `X`, if `E ⊆ X` is stable under specialization,
`Λ` is a Noetherian ring, and `F` is a sheaf of `Λ`-modules on `Xₑₜ` with support contained
in `E`, then `F` is a filtered colimit of constructible sheaves of `Λ`-modules `G` whose
supports lie in closed subsets of `E`. -/
@[stacks 0F0N] #check
  (CategoryTheory.Sheaf.isConstructibleEtaleModule_ind_of_support :
    ∀ {X : Scheme.{u}} [IsNoetherian X]
      {Λ : Type (u + 1)} [Ring Λ] [IsNoetherianRing Λ]
      [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
      {E : Set X}, StableUnderSpecialization E →
      ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        moduleSheafSupport F ⊆ E →
        ObjectProperty.ind.{u + 1}
          (fun G ↦ IsConstructibleEtaleModule
            (fun {Y} f ↦
              ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{u + 1} Λ)
                X.smallEtaleTopology Y.smallEtaleTopology).obj)
            (fun {Y} G ↦ IsFiniteTypeLocallyConstantModule G) G ∧
            ∃ Z : Set X, IsClosed Z ∧ Z ⊆ E ∧ moduleSheafSupport G ⊆ Z) F)

end CategoryTheory.Sheaf
