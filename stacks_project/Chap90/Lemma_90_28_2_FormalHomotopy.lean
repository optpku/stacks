/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalHomotopy

/-! Compatibility checks for power-series cylinders and formal homotopies. -/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

#check (CompleteLocalAlgCat.mvPowerSeries_carrier :
  ∀ (R : CompleteLocalAlgCat Λ k) (r : ℕ),
    (R.mvPowerSeries r).carrier = MvPowerSeries (Fin r) R.carrier)

#check (CompleteLocalAlgCat.mvPowerSeriesC_hom :
  ∀ (R : CompleteLocalAlgCat Λ k) (r : ℕ),
    (R.mvPowerSeriesC r).hom = CompleteLocalAlgCat.mvPowerSeriesCAlgHom R r)

#check (CompleteLocalAlgCat.mvPowerSeriesConstantCoeff_hom :
  ∀ (R : CompleteLocalAlgCat Λ k) (r : ℕ),
    (R.mvPowerSeriesConstantCoeff r).hom =
      CompleteLocalAlgCat.mvPowerSeriesConstantCoeffAlgHom R r)

#check (CompleteLocalAlgCat.mvPowerSeriesC_comp_constantCoeff :
  ∀ (R : CompleteLocalAlgCat Λ k) (r : ℕ),
    R.mvPowerSeriesC r ≫ R.mvPowerSeriesConstantCoeff r = 𝟙 R)

#check (CompleteLocalAlgCat.FormalHomotopy.spec :
  ∀ {R S : CompleteLocalAlgCat Λ k} {f g : R ⟶ S}
    (H : CompleteLocalAlgCat.FormalHomotopy f g),
    H.h ≫ R.mvPowerSeriesConstantCoeff H.r = 𝟙 R ∧
      R.mvPowerSeriesC H.r ≫ H.k = f ∧ H.h ≫ H.k = g)

#check (CompleteLocalAlgCat.FormalHomotopy.compRight :
  ∀ {R S T : CompleteLocalAlgCat Λ k} {f₁ f₂ : R ⟶ S},
    CompleteLocalAlgCat.FormalHomotopy f₁ f₂ → (g : S ⟶ T) →
      CompleteLocalAlgCat.FormalHomotopy (f₁ ≫ g) (f₂ ≫ g))

#check (CompleteLocalAlgCat.FormallyHomotopic.iff :
  ∀ {R S : CompleteLocalAlgCat Λ k} (f g : R ⟶ S),
    CompleteLocalAlgCat.FormallyHomotopic f g ↔
      ∃ (r : ℕ) (h : R ⟶ R.mvPowerSeries r) (eval : R.mvPowerSeries r ⟶ S),
        h ≫ R.mvPowerSeriesConstantCoeff r = 𝟙 R ∧
          R.mvPowerSeriesC r ≫ eval = f ∧ h ≫ eval = g)
