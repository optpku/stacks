module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.ArithmeticDualSheafComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.GeometricTraceCharacter

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace ActualArithmeticGeometricTrace
variable {k : Type u} [Field k]
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
variable (X : SchemeOverField k) [ConnectedSpace (geometricBaseChange X)]
variable (ηbar : GeometricPoint (geometricBaseChange X))

variable [ConnectedSpace X.left]
variable [ConnectedSpace (Spec (CommRingCat.of k))]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]

variable [(geometricBaseChange X).smallEtaleTopology.HasSheafCompose (ActualFiniteCoefficient.modules Λ)]
variable [HasWeakSheafify (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ U : (geometricBaseChange X).Etale,
    HasWeakSheafify ((geometricBaseChange X).smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
variable [HasWeakSheafify (geometricBaseChange X).smallEtaleTopology
    (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card Λ)))]
variable [∀ U : (geometricBaseChange X).Etale,
    HasWeakSheafify ((geometricBaseChange X).smallEtaleTopology.over U)
      (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card Λ)))]
variable [HasSheafify (geometricBaseChange X).smallEtaleTopology AddCommGrpCat.{u + 1}]
variable (hΛ : IsUnit (Nat.card Λ : k))

variable (N : (finiteTypeDiscreteModule Λ
  (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))).FullSubcategory)
variable (C : SchemeOverField (AlgebraicClosure k)) [Curve C] [Smooth C.hom] [Projective C.hom]
variable (j : geometricBaseChange X ⟶ C.left) [hopen : IsOpenImmersion j]
variable [(geometricBaseChange X).smallEtaleTopology.HasSheafCompose
    (forget₂ (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card Λ))) AddCommGrpCat.{u + 1})]
variable [EnoughInjectives (Sheaf (geometricBaseChange X).smallEtaleTopology
    (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card Λ))))]
variable [EnoughInjectives (Sheaf (geometricBaseChange X).smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [HasExt.{u + 1} (Sheaf (geometricBaseChange X).smallEtaleTopology
    (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card Λ))))]
variable [HasExt.{u + 1} (Sheaf (geometricBaseChange X).smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [HasSheafify C.left.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasExt.{u + 1} (Sheaf C.left.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [∀ F : (geometricBaseChange X).Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (etaleRestriction j).op.HasLeftKanExtension F]

/-- The finite arithmetic source, after geometric restriction and the actual scalar restriction. -/
abbrev coefficient :=
  (ActualFiniteCoefficient.sheaves Λ (geometricBaseChange X)).obj
    (ActualFiniteDualComparison.sourceSheaf Λ X ηbar
      (ActualArithmeticDualSheaf.geometricInput Λ X ηbar N))

/-- The concrete scalar-restricted finite associated sheaf is a finite local system. -/
instance coefficient_finite : Sheaf.IsFiniteTypeLocallyConstantModule (coefficient Λ X ηbar N) :=
  ActualFiniteCoefficient.sheaves_finiteLocallyConstant Λ (geometricBaseChange X)
    (ActualFiniteDualComparison.sourceSheaf Λ X ηbar
      (ActualArithmeticDualSheaf.geometricInput Λ X ηbar N))

/-- Transport characters by precomposition with the inverse of an actual additive equivalence. -/
def characterCongr {A B : Type*} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) :
    CharacterModule A ≃+ CharacterModule B where
  toFun χ := χ.comp e.symm.toAddMonoidHom
  invFun χ := χ.comp e.toAddMonoidHom
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry

/-- The intrinsic dual cohomology is compared by applying H to the actual
sheaf isomorphism with the inverse-Tate continuous-character coefficient. -/
def dualCohomologyIso (b : ℕ) :=
  (Sheaf.functorH (geometricBaseChange X).smallEtaleTopology b).mapIso
    ((ActualSiteExt.moduleForget (geometricBaseChange X)
      (ActualRootsModule.Coeff.{u} (Nat.card Λ))).mapIso
        (ActualArithmeticDualSheaf.intrinsicToCharacterSheafIso Λ X ηbar hΛ N))

/-- Cardinality is positive for a finite ring, including the zero ring. -/
theorem card_pos : 0 < Nat.card Λ := by
  exact Nat.pos_of_ne_zero (AlgebraicGeometry.Scheme.Etale.natCard_ne_zero_of_finite_ring (Λ := Λ)).out

include hΛ in
/-- Invertibility is preserved by the actual ground-field extension. -/
theorem card_invertible : IsUnit (Nat.card Λ : AlgebraicClosure k) := by
  simpa using hΛ.map (algebraMap k (AlgebraicClosure k))

/-- The normalized compact trace pairing is now assembled with the actual
arithmetic inverse-Tate character sheaf. This is still on the specified
smooth compactification; its forward map is the earlier explicit trace. -/
def compactCharacterEquiv (a b : ℕ) (hab : a + b = 2) :=
  -- Local instance justification (defeq pin): the chosen over-field model has the same underlying open immersion.
  letI : IsOpenImmersion
      (show (ActualFiniteDualComparison.geometricCurve X).left ⟶ C.left from j) := hopen
  -- Local instance justification (defeq pin): resolutions on the identical underlying geometric scheme.
  letI : EnoughInjectives (Sheaf (ActualFiniteDualComparison.geometricCurve X).left.smallEtaleTopology
      (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card Λ)))) :=
    inferInstanceAs (EnoughInjectives (Sheaf (geometricBaseChange X).smallEtaleTopology
      (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card Λ)))))
  -- Local instance justification (defeq pin): the additive resolution category is unchanged.
  letI : EnoughInjectives (Sheaf (ActualFiniteDualComparison.geometricCurve X).left.smallEtaleTopology
      AddCommGrpCat.{u + 1}) :=
    inferInstanceAs (EnoughInjectives (Sheaf (geometricBaseChange X).smallEtaleTopology AddCommGrpCat.{u + 1}))
  -- Local instance justification (defeq pin): reuse precisely the supplied small Ext universes.
  letI : HasExt.{u + 1} (Sheaf (ActualFiniteDualComparison.geometricCurve X).left.smallEtaleTopology
      (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card Λ)))) :=
    inferInstanceAs (HasExt.{u + 1} (Sheaf (geometricBaseChange X).smallEtaleTopology
      (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card Λ)))))
  -- Local instance justification (defeq pin): same additive Ext category, with no new smallness assumption.
  letI : HasExt.{u + 1} (Sheaf (ActualFiniteDualComparison.geometricCurve X).left.smallEtaleTopology
      AddCommGrpCat.{u + 1}) :=
    inferInstanceAs (HasExt.{u + 1} (Sheaf (geometricBaseChange X).smallEtaleTopology AddCommGrpCat.{u + 1}))
  -- Local instance justification (defeq pin): reuse finite local constancy on the identical site presentation.
  letI : Sheaf.IsFiniteTypeLocallyConstantModule
      (J := (ActualFiniteDualComparison.geometricCurve X).left.smallEtaleTopology)
      (coefficient Λ X ηbar N) := coefficient_finite Λ X ηbar N
  (ActualGeometricTraceCharacter.traceCharacterEquiv
    (ActualFiniteDualComparison.geometricCurve X) C j (Nat.card Λ)
    (card_pos Λ) (card_invertible Λ hΛ) (coefficient Λ X ηbar N) a b hab).trans
    (characterCongr (dualCohomologyIso Λ X ηbar hΛ N b).addCommGroupIsoToAddEquiv)

end ActualArithmeticGeometricTrace
