module

public import ReasLib.AlgebraicGeometry.Crystalline.Completed.Site

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

#check (CompletedCris.crisOppSite γ f hIC h_pC : Type (max u (v + 1)))

#check (CompletedCris.crisWedgeOppSite γ f hIC h_pC : Type (max u (v + 1)))

#check (CompletedCris.ofCrisOp γ f hIC h_pC :
  CompletedCris.crisOppSite γ f hIC h_pC ⥤ CompletedCris.crisWedgeOppSite γ f hIC h_pC)

#check (CompletedCris.ofCrisOp_obj γ f hIC h_pC :
  ∀ T : DividedPowerThickening.Cris γ f hIC h_pC,
    (CompletedCris.ofCrisOp γ f hIC h_pC).obj (op T) =
      op ((CompletedCris.isCrisObject γ f hIC h_pC).ι.obj
        ((CompletedCris.ofCrisFunctor γ f hIC h_pC).obj T)))

#check (CompletedCris.stageAbelianSystem γ f hIC h_pC :
  Sheaf (⊥ : GrothendieckTopology (CompletedCris.crisOppSite γ f hIC h_pC)) AddCommGrpCat.{w} →
    CompletedCrisObject p A I γ C f hIC h_pC → ℕᵒᵖ ⥤ AddCommGrpCat.{w})

#check (CompletedCris.stageAbelianSystem_obj γ f hIC h_pC :
  ∀ (F : Sheaf (⊥ : GrothendieckTopology (CompletedCris.crisOppSite γ f hIC h_pC))
      AddCommGrpCat.{w}) (B : CompletedCrisObject p A I γ C f hIC h_pC) (e : ℕ),
    (CompletedCris.stageAbelianSystem γ f hIC h_pC F B).obj (op e) =
      ((sheafToPresheaf (⊥ : GrothendieckTopology (CompletedCris.crisOppSite γ f hIC h_pC))
        AddCommGrpCat.{w}).obj F).obj (op (op (pAdicQuotientStage γ f hIC h_pC B e))))
