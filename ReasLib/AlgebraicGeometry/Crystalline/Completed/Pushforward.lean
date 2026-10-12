/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Completed.Site
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import Mathlib.CategoryTheory.Sites.Abelian

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace CompletedCris

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {A : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {C : Type v} [CommRing C] (f : A →+* C)
variable (hIC : Ideal.map f I = (⊥ : Ideal C))
variable (h_pC : IsNilpotent (p : C))

section Topos

variable [∀ G : (crisOppSite γ f hIC h_pC)ᵒᵖ ⥤ Type w,
  (ofCrisOp γ f hIC h_pC).op.HasPointwiseRightKanExtension G]

/-- The inclusion of crystalline thickenings induces a morphism from the ordinary chaotic
topos to the completed chaotic topos. -/
def toposMorphism :
    MorphismOfTopoiIn (⊥ : GrothendieckTopology (crisWedgeOppSite γ f hIC h_pC))
      (⊥ : GrothendieckTopology (crisOppSite γ f hIC h_pC)) :=
  (ofCrisOp γ f hIC h_pC).morphismOfTopoiInOfCocontinuous
    (⊥ : GrothendieckTopology (crisOppSite γ f hIC h_pC))
    (⊥ : GrothendieckTopology (crisWedgeOppSite γ f hIC h_pC))

end Topos

section Abelian

variable [∀ G : (crisOppSite γ f hIC h_pC)ᵒᵖ ⥤ AddCommGrpCat.{w},
  (ofCrisOp γ f hIC h_pC).op.HasPointwiseRightKanExtension G]

/-- Direct image of chaotic abelian sheaves along the inclusion into completed crystalline objects. -/
def chaoticCrisPushforward :
    Sheaf (⊥ : GrothendieckTopology (crisOppSite γ f hIC h_pC)) AddCommGrpCat.{w} ⥤
      Sheaf (⊥ : GrothendieckTopology (crisWedgeOppSite γ f hIC h_pC)) AddCommGrpCat.{w} :=
  (ofCrisOp γ f hIC h_pC).sheafPushforwardCocontinuous AddCommGrpCat.{w}
    (⊥ : GrothendieckTopology (crisOppSite γ f hIC h_pC))
    (⊥ : GrothendieckTopology (crisWedgeOppSite γ f hIC h_pC))

/-- The chaotic crystalline direct image is additive on abelian sheaves. -/
instance chaoticCrisPushforward_additive :
    (chaoticCrisPushforward γ f hIC h_pC).Additive := sorry

end Abelian

end CompletedCris
