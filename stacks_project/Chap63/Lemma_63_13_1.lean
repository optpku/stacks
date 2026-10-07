module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import stacks_project.Chap59.Definition_59_71_1_Constructible
public import stacks_project.Chap59.Lemma_59_80_9_Pullback
public import stacks_project.Chap63.Lemma_63_13_1_Frobenius
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale
open Frobenius

variable {S : Scheme.{u}} (p : ℕ) [Fact p.Prime] [S.IsCharP p]
variable (E : S.Modules) [E.IsFiniteLocallyFree]
variable [Abelian (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
variable (F : smallEtaleAbelian S E ⟶ smallEtaleAbelian S E)

/-- Lemma 63.13.1 (1): the cokernel of `F - 𝟙` vanishes for a Frobenius-semilinear
endomorphism of a finite locally free module on `S_étale`. -/
@[stacks 0GKU]
theorem coker_subId_isZero (hF : IsFrobeniusSemilinear p E F) :
    IsZero (cokernel (subId F)) := sorry

/-- Lemma 63.13.1 (2): the kernel of `F - 𝟙` is a constructible abelian sheaf on
`S_étale`. -/
@[stacks 0GKU]
theorem ker_subId_isConstructible (hF : IsFrobeniusSemilinear p E F)
    [∀ (Y : Scheme.{u}) (V : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}] :
    IsConstructibleEtale (fun {Y} f ↦ (etaleAbelianSheafPullback f).obj)
      (fun {Y} G ↦ IsFiniteLocallyConstantAddCommGrp G) (kernel (subId F)) :=
  sorry

end AlgebraicGeometry.Scheme.Etale
