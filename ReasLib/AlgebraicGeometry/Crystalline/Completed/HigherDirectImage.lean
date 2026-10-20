/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Completed.Pushforward
public import ReasLib.CategoryTheory.InverseSystem.Milnor.Derived.Canonical
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.IsomorphismClasses

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
variable [∀ G : (crisOppSite γ f hIC h_pC)ᵒᵖ ⥤ AddCommGrpCat.{w},
  (ofCrisOp γ f hIC h_pC).op.HasPointwiseRightKanExtension G]
variable [HasInjectiveResolutions
  (Sheaf (⊥ : GrothendieckTopology (crisOppSite γ f hIC h_pC)) AddCommGrpCat.{w})]

/-- The cohomological right derived functors of the chaotic crystalline direct image. -/
def derivedChaoticCrisPushforward (n : ℕ) :
    Sheaf (⊥ : GrothendieckTopology (crisOppSite γ f hIC h_pC)) AddCommGrpCat.{w} ⥤
      Sheaf (⊥ : GrothendieckTopology (crisWedgeOppSite γ f hIC h_pC)) AddCommGrpCat.{w} :=
  Functor.rightDerived (chaoticCrisPushforward γ f hIC h_pC) n

/-- Evaluation of the right derived crystalline direct image at a completed object. -/
def derivedDirectImageEval
    (F : Sheaf (⊥ : GrothendieckTopology (crisOppSite γ f hIC h_pC)) AddCommGrpCat.{w})
    (B : CompletedCrisObject p A I γ C f hIC h_pC) (n : ℕ) : AddCommGrpCat.{w} :=
  ((sheafToPresheaf (⊥ : GrothendieckTopology (crisWedgeOppSite γ f hIC h_pC))
    AddCommGrpCat.{w}).obj
      ((derivedChaoticCrisPushforward γ f hIC h_pC n).obj F)).obj (op (op B))

/-- The degree-zero crystalline direct image evaluates to the inverse limit of the shifted
`p`-adic quotient-stage system. -/
theorem derivedDirectImageEval_zero
    (F : Sheaf (⊥ : GrothendieckTopology (crisOppSite γ f hIC h_pC)) AddCommGrpCat.{w})
    (B : CompletedCrisObject p A I γ C f hIC h_pC) :
    IsIsomorphic (derivedDirectImageEval γ f hIC h_pC F B 0)
      (limit (stageAbelianSystem γ f hIC h_pC F B)) := sorry

/-- The degree-one crystalline direct image evaluates to the canonical Milnor cokernel of
the shifted `p`-adic quotient-stage system. -/
theorem derivedDirectImageEval_one
    (F : Sheaf (⊥ : GrothendieckTopology (crisOppSite γ f hIC h_pC)) AddCommGrpCat.{w})
    (B : CompletedCrisObject p A I γ C f hIC h_pC) :
    IsIsomorphic (derivedDirectImageEval γ f hIC h_pC F B 1)
      (SequentialInverseSystem.Milnor.ProductCone.canonicalR1
        (stageAbelianSystem γ f hIC h_pC F B)) := sorry

/-- The evaluated crystalline right derived direct image vanishes in every degree at least two. -/
theorem isZero_derivedDirectImageEval
    (F : Sheaf (⊥ : GrothendieckTopology (crisOppSite γ f hIC h_pC)) AddCommGrpCat.{w})
    (B : CompletedCrisObject p A I γ C f hIC h_pC) (n : ℕ) (hn : 2 ≤ n) :
    IsZero (derivedDirectImageEval γ f hIC h_pC F B n) := sorry

end CompletedCris
