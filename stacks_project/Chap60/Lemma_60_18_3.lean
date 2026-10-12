/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Completed.HigherDirectImage
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CompletedCris

universe u v w

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {A : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {C : Type v} [CommRing C] (f : A →+* C)
variable (hIC : Ideal.map f I = (⊥ : Ideal C))
variable (h_pC : IsNilpotent (p : C))
variable [∀ G : (crisOppSite γ f hIC h_pC)ᵒᵖ ⥤ Type w,
  (ofCrisOp γ f hIC h_pC).op.HasPointwiseRightKanExtension G]
variable [∀ (G : (crisOppSite γ f hIC h_pC)ᵒᵖ ⥤ AddCommGrpCat.{w}),
  (ofCrisOp γ f hIC h_pC).op.HasPointwiseRightKanExtension G]
variable [HasInjectiveResolutions
  (Sheaf (⊥ : GrothendieckTopology (crisOppSite γ f hIC h_pC)) AddCommGrpCat.{w})]

/- Lemma 60.18.3 (1): the morphism of chaotic topoi
`g : Sh(Cris(C/A)ᵒᵖ) ⟶ Sh((Cris^∧(C/A))ᵒᵖ)` induced by `ofCrisOp`. -/
@[stacks 07JL] #check (CompletedCris.toposMorphism γ f hIC h_pC :
  MorphismOfTopoiIn (⊥ : GrothendieckTopology (crisWedgeOppSite γ f hIC h_pC))
    (⊥ : GrothendieckTopology (crisOppSite γ f hIC h_pC)))

/- Lemma 60.18.3 (2): the value of `R^0 g_* F` at a completed object is the inverse limit
of its shifted `p`-adic quotient-stage system. -/
@[stacks 07JL] #check (CompletedCris.derivedDirectImageEval_zero γ f hIC h_pC :
  ∀ (F : Sheaf (⊥ : GrothendieckTopology (crisOppSite γ f hIC h_pC)) AddCommGrpCat.{w})
    (B : CompletedCrisObject p A I γ C f hIC h_pC),
    IsIsomorphic (CompletedCris.derivedDirectImageEval γ f hIC h_pC F B 0)
      (limit (CompletedCris.stageAbelianSystem γ f hIC h_pC F B)))

/- Lemma 60.18.3 (3): the value of `R^1 g_* F` at a completed object is the first derived
inverse limit of its shifted `p`-adic quotient-stage system. -/
@[stacks 07JL] #check (CompletedCris.derivedDirectImageEval_one γ f hIC h_pC :
  ∀ (F : Sheaf (⊥ : GrothendieckTopology (crisOppSite γ f hIC h_pC)) AddCommGrpCat.{w})
    (B : CompletedCrisObject p A I γ C f hIC h_pC),
    IsIsomorphic (CompletedCris.derivedDirectImageEval γ f hIC h_pC F B 1)
      (SequentialInverseSystem.Milnor.ProductCone.canonicalR1
        (CompletedCris.stageAbelianSystem γ f hIC h_pC F B)))

/- Lemma 60.18.3 (4): the values of `R^n g_* F` at completed objects vanish for `n ≥ 2`. -/
@[stacks 07JL] #check (CompletedCris.isZero_derivedDirectImageEval γ f hIC h_pC :
  ∀ (F : Sheaf (⊥ : GrothendieckTopology (crisOppSite γ f hIC h_pC)) AddCommGrpCat.{w})
    (B : CompletedCrisObject p A I γ C f hIC h_pC) (n : ℕ),
    2 ≤ n → IsZero (CompletedCris.derivedDirectImageEval γ f hIC h_pC F B n))
