module

public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import ReasLib.RingTheory.MvPowerSeries.Noetherian
public import stacks_project.Chap10.Remark_10_160_9
public import stacks_project.Chap90.Definition_90_7_3_CompleteLocal

/-!
# Formal homotopy in `CompleteLocalAlgCat`

A formal homotopy between morphisms `f, g : R ⟶ S` in `CompleteLocalAlgCat Λ k` is a
triple `(r, h, k)` with cylinder object `R.mvPowerSeries r` representing
`R[[t₁,…,tᵣ]]`, together with morphisms `h : R ⟶ R[[t₁,…,tᵣ]]` and
`k : R[[t₁,…,tᵣ]] ⟶ S` satisfying the constant-coefficient, inclusion, and
evaluation identities from the Stacks definition.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

noncomputable section

/-- The canonical `Λ`-algebra map `R → R[[t₁,…,tᵣ]]` given by `MvPowerSeries.C`. -/
def mvPowerSeriesCAlgHom (R : CompleteLocalAlgCat Λ k) (r : ℕ) :
    R.carrier →ₐ[Λ] MvPowerSeries (Fin r) R.carrier where
  toRingHom := MvPowerSeries.C
  commutes' := sorry

/-- Constant series `MvPowerSeries.C` is a local homomorphism. -/
instance instIsLocalHom_mvPowerSeriesCAlgHom (R : CompleteLocalAlgCat Λ k) (r : ℕ) :
    IsLocalHom (mvPowerSeriesCAlgHom R r) := sorry

/-- The canonical `Λ`-algebra map `R[[t₁,…,tᵣ]] → R` given by `MvPowerSeries.constantCoeff`. -/
def mvPowerSeriesConstantCoeffAlgHom (R : CompleteLocalAlgCat Λ k) (r : ℕ) :
    MvPowerSeries (Fin r) R.carrier →ₐ[Λ] R.carrier where
  toRingHom := MvPowerSeries.constantCoeff
  commutes' := sorry

/-- The constant-coefficient map is a local homomorphism. -/
instance instIsLocalHom_mvPowerSeriesConstantCoeffAlgHom
    (R : CompleteLocalAlgCat Λ k) (r : ℕ) :
    IsLocalHom (mvPowerSeriesConstantCoeffAlgHom R r) := sorry

/-- Residue identification of `R[[t₁,…,tᵣ]]` with `k`, via constant coefficients and
the residue identification of `R`. -/
def mvPowerSeriesResidueFieldIso (R : CompleteLocalAlgCat Λ k) (r : ℕ) :
    ResidueField (MvPowerSeries (Fin r) R.carrier) ≃ₐ[Λ] k :=
  (AlgEquiv.ofAlgHom
      (ResidueField.mapAlgHom (mvPowerSeriesConstantCoeffAlgHom R r))
      (ResidueField.mapAlgHom (mvPowerSeriesCAlgHom R r)) sorry sorry).trans
    R.residueFieldIso

/-- The power-series cylinder `R[[t₁,…,tᵣ]]` as an object of `CompleteLocalAlgCat Λ k`. -/
def mvPowerSeries (R : CompleteLocalAlgCat Λ k) (r : ℕ) :
    CompleteLocalAlgCat Λ k :=
  of (MvPowerSeries (Fin r) R.carrier) (mvPowerSeriesResidueFieldIso R r)

/-- The carrier of the cylinder object is the multivariate power-series ring. -/
theorem mvPowerSeries_carrier (R : CompleteLocalAlgCat Λ k) (r : ℕ) :
    (R.mvPowerSeries r).carrier = MvPowerSeries (Fin r) R.carrier := sorry

/-- Canonical inclusion `R ⟶ R[[t₁,…,tᵣ]]` in `CompleteLocalAlgCat Λ k`. -/
def mvPowerSeriesC (R : CompleteLocalAlgCat Λ k) (r : ℕ) :
    R ⟶ R.mvPowerSeries r where
  hom := mvPowerSeriesCAlgHom R r
  isLocalHom := sorry
  residue_compat := sorry

/-- Constant-coefficient projection `R[[t₁,…,tᵣ]] ⟶ R` in `CompleteLocalAlgCat Λ k`. -/
def mvPowerSeriesConstantCoeff (R : CompleteLocalAlgCat Λ k) (r : ℕ) :
    R.mvPowerSeries r ⟶ R where
  hom := mvPowerSeriesConstantCoeffAlgHom R r
  isLocalHom := sorry
  residue_compat := sorry

/-- The underlying algebra map of the canonical inclusion is `mvPowerSeriesCAlgHom`. -/
theorem mvPowerSeriesC_hom (R : CompleteLocalAlgCat Λ k) (r : ℕ) :
    (R.mvPowerSeriesC r).hom = mvPowerSeriesCAlgHom R r := sorry

/-- The underlying algebra map of the constant-coefficient projection is
`mvPowerSeriesConstantCoeffAlgHom`. -/
theorem mvPowerSeriesConstantCoeff_hom (R : CompleteLocalAlgCat Λ k) (r : ℕ) :
    (R.mvPowerSeriesConstantCoeff r).hom = mvPowerSeriesConstantCoeffAlgHom R r := sorry

/-- The constant-coefficient projection retracts the canonical inclusion. -/
theorem mvPowerSeriesC_comp_constantCoeff (R : CompleteLocalAlgCat Λ k) (r : ℕ) :
    R.mvPowerSeriesC r ≫ R.mvPowerSeriesConstantCoeff r = 𝟙 R := sorry

/-- A formal homotopy between morphisms `f, g : R ⟶ S` in `CompleteLocalAlgCat Λ k`. -/
structure FormalHomotopy {R S : CompleteLocalAlgCat Λ k} (f g : R ⟶ S) where
  /-- Number of power-series variables. -/
  r : ℕ
  /-- Cylinder map `R ⟶ R[[t₁,…,tᵣ]]`. -/
  h : R ⟶ R.mvPowerSeries r
  /-- Evaluation map `R[[t₁,…,tᵣ]] ⟶ S`. -/
  k : R.mvPowerSeries r ⟶ S
  /-- The cylinder map reduces to the identity modulo `(t₁,…,tᵣ)`. -/
  h_comp_constantCoeff : h ≫ R.mvPowerSeriesConstantCoeff r = 𝟙 R
  /-- Postcomposing the canonical inclusion with `k` recovers `f`. -/
  C_comp_k : R.mvPowerSeriesC r ≫ k = f
  /-- Postcomposing the cylinder map with `k` recovers `g`. -/
  h_comp_k : h ≫ k = g

/-- The three defining identities of a formal homotopy. -/
theorem FormalHomotopy.spec {R S : CompleteLocalAlgCat Λ k} {f g : R ⟶ S}
    (H : FormalHomotopy f g) :
    H.h ≫ R.mvPowerSeriesConstantCoeff H.r = 𝟙 R ∧
      R.mvPowerSeriesC H.r ≫ H.k = f ∧
      H.h ≫ H.k = g := sorry

/-- Right composition of a formal homotopy with a morphism of targets. -/
def FormalHomotopy.compRight {R S T : CompleteLocalAlgCat Λ k} {f₁ f₂ : R ⟶ S}
    (H : FormalHomotopy f₁ f₂) (g : S ⟶ T) :
    FormalHomotopy (f₁ ≫ g) (f₂ ≫ g) where
  r := H.r
  h := H.h
  k := H.k ≫ g
  h_comp_constantCoeff := H.h_comp_constantCoeff
  C_comp_k := sorry
  h_comp_k := sorry

/-- Morphisms of `CompleteLocalAlgCat Λ k` are formally homotopic when a formal homotopy exists. -/
def FormallyHomotopic {R S : CompleteLocalAlgCat Λ k} (f g : R ⟶ S) : Prop :=
  Nonempty (FormalHomotopy f g)

/-- Formal homotopy of morphisms is equivalent to the existence of a cylinder triple
`(r, h, k)` satisfying the three source identities. -/
theorem FormallyHomotopic.iff {R S : CompleteLocalAlgCat Λ k} (f g : R ⟶ S) :
    FormallyHomotopic f g ↔
      ∃ (r : ℕ) (h : R ⟶ R.mvPowerSeries r) (k : R.mvPowerSeries r ⟶ S),
        h ≫ R.mvPowerSeriesConstantCoeff r = 𝟙 R ∧
          R.mvPowerSeriesC r ≫ k = f ∧
          h ≫ k = g := sorry

end

end CompleteLocalAlgCat
