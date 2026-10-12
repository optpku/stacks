/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DividedPowers.CrystallineCompletion
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Grothendieck
public import ReasLib.CategoryTheory.Sites.Chaotic

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {A : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {C : Type v} [CommRing C] (f : A →+* C)
variable (hIC : Ideal.map f I = (⊥ : Ideal C))
variable (h_pC : IsNilpotent (p : C))

namespace CompletedCris

/-- The opposite category of crystalline thickenings, endowed with the chaotic topology. -/
abbrev crisOppSite := (DividedPowerThickening.Cris γ f hIC h_pC)ᵒᵖ

/-- The opposite category of completed crystalline thickenings, endowed with the chaotic topology. -/
abbrev crisWedgeOppSite := (CompletedCrisObject p A I γ C f hIC h_pC)ᵒᵖ

/-- The inclusion of nilpotent crystalline thickenings into completed thickenings on opposites. -/
def ofCrisOp : crisOppSite γ f hIC h_pC ⥤ crisWedgeOppSite γ f hIC h_pC :=
  (ofCrisFunctor γ f hIC h_pC ⋙ (isCrisObject γ f hIC h_pC).ι).op

/-- The inclusion on opposite categories sends a thickening to its completed crystalline object. -/
theorem ofCrisOp_obj (T : DividedPowerThickening.Cris γ f hIC h_pC) :
    (ofCrisOp γ f hIC h_pC).obj (op T) =
      op ((isCrisObject γ f hIC h_pC).ι.obj ((ofCrisFunctor γ f hIC h_pC).obj T)) := sorry

/-- The inverse system of abelian sheaf values along the shifted crystalline `p`-adic quotients. -/
def stageAbelianSystem
    (F : Sheaf (⊥ : GrothendieckTopology (crisOppSite γ f hIC h_pC)) AddCommGrpCat.{w})
    (B : CompletedCrisObject p A I γ C f hIC h_pC) :
    ℕᵒᵖ ⥤ AddCommGrpCat.{w} :=
  pAdicQuotientSystem γ f hIC h_pC B ⋙
    opOp (DividedPowerThickening.Cris γ f hIC h_pC) ⋙
      (sheafToPresheaf (⊥ : GrothendieckTopology (crisOppSite γ f hIC h_pC))
        AddCommGrpCat.{w}).obj F

/-- At each stage the inverse system is the sheaf evaluated on the corresponding `p`-adic quotient. -/
theorem stageAbelianSystem_obj
    (F : Sheaf (⊥ : GrothendieckTopology (crisOppSite γ f hIC h_pC)) AddCommGrpCat.{w})
    (B : CompletedCrisObject p A I γ C f hIC h_pC) (e : ℕ) :
    (stageAbelianSystem γ f hIC h_pC F B).obj (op e) =
      ((sheafToPresheaf (⊥ : GrothendieckTopology (crisOppSite γ f hIC h_pC))
          AddCommGrpCat.{w}).obj F).obj
        (op (op (pAdicQuotientStage γ f hIC h_pC B e))) := sorry

end CompletedCris
