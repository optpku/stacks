/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal
public import ReasLib.RingTheory.MvPowerSeries.Noetherian
public import Mathlib.RingTheory.MvPowerSeries.Inverse

/-!
# Formal homotopies of complete local algebras

Finite-variable power-series cylinders carry a coefficient inclusion and a
constant-coefficient retraction. Formal homotopies are explicit cylinder triples;
postcomposition changes only their evaluation morphism.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

noncomputable section

/-- Finite-variable power series over a Noetherian complete local algebra are
complete for their maximal-adic topology. -/
instance instIsCompleteLocalRingMvPowerSeries (R : CompleteLocalAlgCat Λ k) (r : ℕ) :
    IsCompleteLocalRing (MvPowerSeries (Fin r) R.carrier) := sorry

/-- The coefficient inclusion of a finite-variable power-series algebra. -/
def mvPowerSeriesCAlgHom (R : CompleteLocalAlgCat Λ k) (r : ℕ) :
    @AlgHom Λ R.carrier (MvPowerSeries (Fin r) R.carrier) _ _ _
      R.algebra (@MvPowerSeries.instAlgebra (Fin r) Λ R.carrier _ _ R.algebra) :=
  @AlgHom.mk Λ R.carrier (MvPowerSeries (Fin r) R.carrier) _ _ _
    R.algebra (@MvPowerSeries.instAlgebra (Fin r) Λ R.carrier _ _ R.algebra)
    MvPowerSeries.C sorry

/-- The coefficient inclusion is a local homomorphism. -/
instance instIsLocalHom_mvPowerSeriesCAlgHom (R : CompleteLocalAlgCat Λ k) (r : ℕ) :
    IsLocalHom (mvPowerSeriesCAlgHom R r) := sorry

/-- The constant-coefficient projection of a finite-variable power-series algebra. -/
def mvPowerSeriesConstantCoeffAlgHom (R : CompleteLocalAlgCat Λ k) (r : ℕ) :
    @AlgHom Λ (MvPowerSeries (Fin r) R.carrier) R.carrier _ _ _
      (@MvPowerSeries.instAlgebra (Fin r) Λ R.carrier _ _ R.algebra) R.algebra :=
  @AlgHom.mk Λ (MvPowerSeries (Fin r) R.carrier) R.carrier _ _ _
    (@MvPowerSeries.instAlgebra (Fin r) Λ R.carrier _ _ R.algebra) R.algebra
    MvPowerSeries.constantCoeff sorry

/-- The constant-coefficient projection is a local homomorphism. -/
instance instIsLocalHom_mvPowerSeriesConstantCoeffAlgHom
    (R : CompleteLocalAlgCat Λ k) (r : ℕ) :
    IsLocalHom (mvPowerSeriesConstantCoeffAlgHom R r) := sorry

/-- Constant coefficients identify the residue field of a finite-variable
power-series algebra with the chosen residue field of its coefficient algebra. -/
def mvPowerSeriesResidueFieldIso (R : CompleteLocalAlgCat Λ k) (r : ℕ) :
    @AlgEquiv Λ
      (@ResidueField (MvPowerSeries (Fin r) R.carrier) _
        (@MvPowerSeries.instIsLocalRing (Fin r) R.carrier _ R.isLocalRing)) k _ _ _
      (@ResidueField.algebra (MvPowerSeries (Fin r) R.carrier) _
        (@MvPowerSeries.instIsLocalRing (Fin r) R.carrier _ R.isLocalRing) Λ _
        (@MvPowerSeries.instAlgebra (Fin r) Λ R.carrier _ _ R.algebra)) _ :=
  let seriesAlgebra := @MvPowerSeries.instAlgebra (Fin r) Λ R.carrier _ _ R.algebra
  let seriesLocalRing := @MvPowerSeries.instIsLocalRing (Fin r) R.carrier _ R.isLocalRing
  let seriesResidueAlgebra :=
    @ResidueField.algebra (MvPowerSeries (Fin r) R.carrier) _ seriesLocalRing Λ _ seriesAlgebra
  let coefficientResidueAlgebra :=
    @ResidueField.algebra R.carrier _ R.isLocalRing Λ _ R.algebra
  @AlgEquiv.trans Λ _ _ k _ _ _ _ seriesResidueAlgebra coefficientResidueAlgebra _
    (@AlgEquiv.ofAlgHom Λ _ _ _ _ _ seriesResidueAlgebra coefficientResidueAlgebra
      (@ResidueField.mapAlgHom Λ (MvPowerSeries (Fin r) R.carrier) R.carrier
        _ _ seriesLocalRing _ R.isLocalRing seriesAlgebra R.algebra
        (mvPowerSeriesConstantCoeffAlgHom R r)
        (instIsLocalHom_mvPowerSeriesConstantCoeffAlgHom R r))
      (@ResidueField.mapAlgHom Λ R.carrier (MvPowerSeries (Fin r) R.carrier)
        _ _ R.isLocalRing _ seriesLocalRing R.algebra seriesAlgebra
        (mvPowerSeriesCAlgHom R r) (instIsLocalHom_mvPowerSeriesCAlgHom R r))
      sorry sorry) R.residueFieldIso

/-- The finite-variable power-series cylinder of a complete local algebra,
with its induced algebra structure and residue identification. -/
def mvPowerSeries (R : CompleteLocalAlgCat Λ k) (r : ℕ) :
    CompleteLocalAlgCat Λ k :=
  @of Λ k _ _ _ _ _ (MvPowerSeries (Fin r) R.carrier) _
    (@MvPowerSeries.instAlgebra (Fin r) Λ R.carrier _ _ R.algebra)
    (@MvPowerSeries.instIsNoetherianRing R.carrier _ (Fin r) _ R.isNoetherianRing)
    (instIsCompleteLocalRingMvPowerSeries R r) (mvPowerSeriesResidueFieldIso R r)

/-- The carrier of a power-series cylinder is the finite-variable power-series ring. -/
theorem mvPowerSeries_carrier (R : CompleteLocalAlgCat Λ k) (r : ℕ) :
    (R.mvPowerSeries r).carrier = MvPowerSeries (Fin r) R.carrier := sorry

/-- The coefficient inclusion as a residue-compatible morphism of complete local algebras. -/
def mvPowerSeriesC (R : CompleteLocalAlgCat Λ k) (r : ℕ) :
    R ⟶ R.mvPowerSeries r :=
  Hom.of (mvPowerSeriesCAlgHom R r) (instIsLocalHom_mvPowerSeriesCAlgHom R r) sorry

/-- The constant-coefficient projection as a residue-compatible morphism of
complete local algebras. -/
def mvPowerSeriesConstantCoeff (R : CompleteLocalAlgCat Λ k) (r : ℕ) :
    R.mvPowerSeries r ⟶ R :=
  Hom.of (mvPowerSeriesConstantCoeffAlgHom R r)
    (instIsLocalHom_mvPowerSeriesConstantCoeffAlgHom R r) sorry

/-- The underlying algebra map of the cylinder inclusion is the coefficient inclusion. -/
theorem mvPowerSeriesC_hom (R : CompleteLocalAlgCat Λ k) (r : ℕ) :
    (R.mvPowerSeriesC r).hom = mvPowerSeriesCAlgHom R r := sorry

/-- The underlying algebra map of the cylinder projection is the constant-coefficient map. -/
theorem mvPowerSeriesConstantCoeff_hom (R : CompleteLocalAlgCat Λ k) (r : ℕ) :
    (R.mvPowerSeriesConstantCoeff r).hom = mvPowerSeriesConstantCoeffAlgHom R r := sorry

/-- The constant-coefficient projection retracts the coefficient inclusion. -/
theorem mvPowerSeriesC_comp_constantCoeff (R : CompleteLocalAlgCat Λ k) (r : ℕ) :
    R.mvPowerSeriesC r ≫ R.mvPowerSeriesConstantCoeff r = 𝟙 R := sorry

/-- A formal homotopy is a finite-variable cylinder triple relating two
morphisms of complete local algebras. -/
structure FormalHomotopy {R S : CompleteLocalAlgCat Λ k} (f g : R ⟶ S) where
  /-- The number of power-series variables. -/
  r : ℕ
  /-- The cylinder map out of the coefficient algebra. -/
  h : R ⟶ R.mvPowerSeries r
  /-- The evaluation map from the cylinder to the target algebra. -/
  k : R.mvPowerSeries r ⟶ S
  /-- The cylinder map reduces to the identity under constant coefficients. -/
  h_comp_constantCoeff : h ≫ R.mvPowerSeriesConstantCoeff r = 𝟙 R
  /-- Evaluating the coefficient inclusion recovers the first morphism. -/
  C_comp_k : R.mvPowerSeriesC r ≫ k = f
  /-- Evaluating the cylinder map recovers the second morphism. -/
  h_comp_k : h ≫ k = g

/-- A formal homotopy satisfies the constant-coefficient retraction and both
evaluation identities. -/
theorem FormalHomotopy.spec {R S : CompleteLocalAlgCat Λ k} {f g : R ⟶ S}
    (H : FormalHomotopy f g) :
    H.h ≫ R.mvPowerSeriesConstantCoeff H.r = 𝟙 R ∧
      R.mvPowerSeriesC H.r ≫ H.k = f ∧ H.h ≫ H.k = g := sorry

/-- Postcomposing the evaluation map of a formal homotopy preserves its
number of variables and cylinder map. -/
def FormalHomotopy.compRight {R S T : CompleteLocalAlgCat Λ k} {f₁ f₂ : R ⟶ S}
    (H : FormalHomotopy f₁ f₂) (g : S ⟶ T) :
    FormalHomotopy (f₁ ≫ g) (f₂ ≫ g) where
  r := H.r
  h := H.h
  k := H.k ≫ g
  h_comp_constantCoeff := H.h_comp_constantCoeff
  C_comp_k := sorry
  h_comp_k := sorry

/-- Morphisms of complete local algebras are formally homotopic when an
explicit formal homotopy exists. -/
def FormallyHomotopic {R S : CompleteLocalAlgCat Λ k} (f g : R ⟶ S) : Prop :=
  Nonempty (FormalHomotopy f g)

/-- Formal homotopy is equivalent to the existence of a finite-variable
cylinder triple satisfying the retraction and evaluation identities. -/
theorem FormallyHomotopic.iff {R S : CompleteLocalAlgCat Λ k} (f g : R ⟶ S) :
    FormallyHomotopic f g ↔
      ∃ (r : ℕ) (h : R ⟶ R.mvPowerSeries r) (k : R.mvPowerSeries r ⟶ S),
        h ≫ R.mvPowerSeriesConstantCoeff r = 𝟙 R ∧
          R.mvPowerSeriesC r ≫ k = f ∧ h ≫ k = g := sorry

/-- Postcomposition by a morphism of complete local algebras preserves
formal homotopy. -/
theorem FormallyHomotopic.compRight {R S S' : CompleteLocalAlgCat Λ k}
    {f₁ f₂ : R ⟶ S} (h : FormallyHomotopic f₁ f₂) (g : S ⟶ S') :
    FormallyHomotopic (f₁ ≫ g) (f₂ ≫ g) := sorry

end

end CompleteLocalAlgCat
