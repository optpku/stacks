/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DividedPowers.Envelope.Completion
public import Mathlib.CategoryTheory.EqToHom

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits DividedPowers Opposite

universe u

namespace DividedPowers.PAdic

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (A P : Type u) [CommRing A] [CommRing P]
variable (I : Ideal A) (γ : DividedPowers I)
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable [Algebra A P]
variable (C : Type u) [CommRing C]
variable (f : A →+* C) (π : P →+* C)
variable (hπ_A : π.comp (algebraMap A P) = f)
variable (hIC : Ideal.map f I = (⊥ : Ideal C))
variable (J : Ideal P) (hJ : J = RingHom.ker π)
variable (hIJ : Ideal.map (algebraMap A P) I ≤ J)
/-- The quotient-power tower stage agrees with the corresponding envelope quotient. -/
theorem quotientTower_stage_eq_envelopeQuotient
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (hstablePow : IsStableUnderPowers E.D.dividedPowers
      (Ideal.span {(p : E.D)}) N)
    (e : ℕ)
    (hstable : DividedPowers.IsSubDPIdeal E.D.dividedPowers
      (Ideal.span {(p : E.D)} ^ (e + N) ⊓ E.D.ideal)) :
    DividedPowers.QuotientPowerTower.stage E.D.dividedPowers
        (Ideal.span {(p : E.D)}) N hstablePow e =
      envelopeQuotient p A P I γ J hIJ E (e + N) hstable := sorry

/-- The named identification of the inverse-limit tower stage with `D / p^{e+N} D`. -/
noncomputable def quotientTowerStageIsoEnvelopeQuotient
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (hstablePow : IsStableUnderPowers E.D.dividedPowers
      (Ideal.span {(p : E.D)}) N)
    (e : ℕ)
    (hstable : DividedPowers.IsSubDPIdeal E.D.dividedPowers
      (Ideal.span {(p : E.D)} ^ (e + N) ⊓ E.D.ideal)) :
    DividedPowers.QuotientPowerTower.stage E.D.dividedPowers
        (Ideal.span {(p : E.D)}) N hstablePow e ≅
      envelopeQuotient p A P I γ J hIJ E (e + N) hstable :=
  eqToIso
    (quotientTower_stage_eq_envelopeQuotient p A P I γ J hIJ E N hN hstablePow e
      hstable)


/-- The envelope map `P → D` annihilates `p^e` after quotienting `D`. -/
theorem stagePresentationToEnvelopeQuotient_ker
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ) (e : ℕ) :
    Ideal.span {((p : P) ^ e)} ≤
      RingHom.ker ((Ideal.Quotient.mk (Ideal.span {(p : E.D)} ^ e)).comp E.toD) := sorry

/-- The presentation `P_e → D / p^e D` induced by the envelope. -/
noncomputable def stagePresentationToEnvelopeQuotient
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ) (e : ℕ)
    (hstable : DividedPowers.IsSubDPIdeal E.D.dividedPowers
      (Ideal.span {(p : E.D)} ^ e ⊓ E.D.ideal)) :
    quotient p P e →+* envelopeQuotient p A P I γ J hIJ E e hstable :=
  Ideal.Quotient.lift _
    ((Ideal.Quotient.mk (Ideal.span {(p : E.D)} ^ e)).comp E.toD)
    (stagePresentationToEnvelopeQuotient_ker p A P I γ J hIJ E e)

/-- The presentation map from `P_e` is a divided-power morphism after composing with `stageMap`. -/
theorem stagePresentationToEnvelopeQuotient_isDPMorphism
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ) (e : ℕ)
    (hstable : DividedPowers.IsSubDPIdeal E.D.dividedPowers
      (Ideal.span {(p : E.D)} ^ e ⊓ E.D.ideal)) :
    DividedPowers.IsDPMorphism γ
      (envelopeQuotient p A P I γ J hIJ E e hstable).dividedPowers
      ((stagePresentationToEnvelopeQuotient p A P I γ J hIJ E e hstable).comp
        (stageMap p A P e)) := sorry

/-- The image of `J_e` lands in the distinguished ideal of `D / p^e D`. -/
theorem stagePresentationToEnvelopeQuotient_ideal
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ) (e : ℕ)
    (hstable : DividedPowers.IsSubDPIdeal E.D.dividedPowers
      (Ideal.span {(p : E.D)} ^ e ⊓ E.D.ideal)) :
    Ideal.map (stagePresentationToEnvelopeQuotient p A P I γ J hIJ E e hstable)
        (stageIdeal p P J e) ≤
      (envelopeQuotient p A P I γ J hIJ E e hstable).ideal := sorry

/-- The unique envelope map `D_e ⟶ D / p^e D`. -/
noncomputable def stageToEnvelopeQuotient
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ) (e : ℕ)
    (hstable : DividedPowers.IsSubDPIdeal E.D.dividedPowers
      (Ideal.span {(p : E.D)} ^ e ⊓ E.D.ideal))
    (EStage : envelopeStage p A P I γ J hIJ e)
    (hEStage : DividedPowerEnvelope.IsUniversal γ (stageMap p A P e)
      (stageIdeal_contains_base p A P I J hIJ e) EStage) :
    EStage.D ⟶ envelopeQuotient p A P I γ J hIJ E e hstable :=
  Classical.choose <| ExistsUnique.exists <|
    hEStage (stagePresentationToEnvelopeQuotient p A P I γ J hIJ E e hstable)
      (stagePresentationToEnvelopeQuotient_isDPMorphism p A P I γ J hIJ E e hstable)
      (stagePresentationToEnvelopeQuotient_ideal p A P I γ J hIJ E e hstable)

/-- The presentation `P → D_e` is a divided-power morphism after composing with the base map. -/
theorem presentationToStage_isDPMorphism
    (hIJ : Ideal.map (algebraMap A P) I ≤ J) (e : ℕ)
    (EStage : envelopeStage p A P I γ J hIJ e) :
    DividedPowers.IsDPMorphism γ EStage.D.dividedPowers
      ((envelopeStageFromP p e EStage).comp (algebraMap A P)) := sorry

/-- The image of `J` lands in the distinguished ideal of `D_e`. -/
theorem presentationToStage_ideal
    (hIJ : Ideal.map (algebraMap A P) I ≤ J) (e : ℕ)
    (EStage : envelopeStage p A P I γ J hIJ e) :
    Ideal.map (envelopeStageFromP p e EStage) J ≤ EStage.D.ideal := sorry

/-- The unique envelope map `D ⟶ D_e`. -/
noncomputable def envelopeToStage
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A P) hIJ E)
    (e : ℕ) (EStage : envelopeStage p A P I γ J hIJ e) :
    E.D ⟶ EStage.D :=
  Classical.choose <| ExistsUnique.exists <|
    hE (envelopeStageFromP p e EStage)
      (presentationToStage_isDPMorphism p A P I γ J hIJ e EStage)
      (presentationToStage_ideal p A P I γ J hIJ e EStage)

/-- The unique envelope map annihilates `p^e` in `D`. -/
theorem envelopeToStage_ker
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A P) hIJ E)
    (e : ℕ) (EStage : envelopeStage p A P I γ J hIJ e) :
    Ideal.span {(p : E.D)} ^ e ≤ RingHom.ker (envelopeToStage p A P I γ J hIJ E hE e EStage).toRingHom := sorry

/-- The induced ring map `D / p^e D → D_e`. -/
noncomputable def envelopeQuotientToStageRingHom
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A P) hIJ E)
    (e : ℕ)
    (hstable : DividedPowers.IsSubDPIdeal E.D.dividedPowers
      (Ideal.span {(p : E.D)} ^ e ⊓ E.D.ideal))
    (EStage : envelopeStage p A P I γ J hIJ e) :
    envelopeQuotient p A P I γ J hIJ E e hstable →+* EStage.D :=
  Ideal.Quotient.lift _
    (envelopeToStage p A P I γ J hIJ E hE e EStage).toRingHom
    (envelopeToStage_ker p A P I γ J hIJ E hE e EStage)

/-- The induced ring map `D / p^e D → D_e` preserves divided powers. -/
theorem envelopeQuotientToStageRingHom_isDPMorphism
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A P) hIJ E)
    (e : ℕ)
    (hstable : DividedPowers.IsSubDPIdeal E.D.dividedPowers
      (Ideal.span {(p : E.D)} ^ e ⊓ E.D.ideal))
    (EStage : envelopeStage p A P I γ J hIJ e) :
    DividedPowers.IsDPMorphism
      (envelopeQuotient p A P I γ J hIJ E e hstable).dividedPowers
      EStage.D.dividedPowers
      (envelopeQuotientToStageRingHom p A P I γ J hIJ E hE e hstable EStage) := sorry

/-- The named divided-power morphism `D / p^e D ⟶ D_e`. -/
noncomputable def envelopeQuotientToStage
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A P) hIJ E)
    (e : ℕ)
    (hstable : DividedPowers.IsSubDPIdeal E.D.dividedPowers
      (Ideal.span {(p : E.D)} ^ e ⊓ E.D.ideal))
    (EStage : envelopeStage p A P I γ J hIJ e) :
    envelopeQuotient p A P I γ J hIJ E e hstable ⟶ EStage.D :=
  DividedPowers.DPMorphism.mk'
    (envelopeQuotientToStageRingHom_isDPMorphism p A P I γ J hIJ E hE e hstable EStage)

/-- The quotient-to-stage map followed by its inverse is the identity. -/
theorem envelopeStage_hom_inv_id
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A P) hIJ E)
    (e : ℕ)
    (hstable : DividedPowers.IsSubDPIdeal E.D.dividedPowers
      (Ideal.span {(p : E.D)} ^ e ⊓ E.D.ideal))
    (EStage : envelopeStage p A P I γ J hIJ e)
    (hEStage : DividedPowerEnvelope.IsUniversal γ (stageMap p A P e)
      (stageIdeal_contains_base p A P I J hIJ e) EStage) :
    envelopeQuotientToStage p A P I γ J hIJ E hE e hstable EStage ≫
      stageToEnvelopeQuotient p A P I γ J hIJ E e hstable EStage hEStage = 𝟙 _ := sorry

/-- The stage-to-quotient comparison is inverse to the quotient-to-stage map. -/
theorem envelopeStage_inv_hom_id
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A P) hIJ E)
    (e : ℕ)
    (hstable : DividedPowers.IsSubDPIdeal E.D.dividedPowers
      (Ideal.span {(p : E.D)} ^ e ⊓ E.D.ideal))
    (EStage : envelopeStage p A P I γ J hIJ e)
    (hEStage : DividedPowerEnvelope.IsUniversal γ (stageMap p A P e)
      (stageIdeal_contains_base p A P I J hIJ e) EStage) :
    stageToEnvelopeQuotient p A P I γ J hIJ E e hstable EStage hEStage ≫
      envelopeQuotientToStage p A P I γ J hIJ E hE e hstable EStage = 𝟙 _ := sorry

/-- The finite envelope quotient is isomorphic to its universal stage. -/
noncomputable def envelopeQuotientIsoStage
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A P) hIJ E)
    (e : ℕ)
    (hstable : DividedPowers.IsSubDPIdeal E.D.dividedPowers
      (Ideal.span {(p : E.D)} ^ e ⊓ E.D.ideal))
    (EStage : envelopeStage p A P I γ J hIJ e)
    (hEStage : DividedPowerEnvelope.IsUniversal γ (stageMap p A P e)
      (stageIdeal_contains_base p A P I J hIJ e) EStage) :
    envelopeQuotient p A P I γ J hIJ E e hstable ≅ EStage.D where
  hom := envelopeQuotientToStage p A P I γ J hIJ E hE e hstable EStage
  inv := stageToEnvelopeQuotient p A P I γ J hIJ E e hstable EStage hEStage
  hom_inv_id := envelopeStage_hom_inv_id p A P I γ J hIJ E hE e hstable EStage hEStage
  inv_hom_id := envelopeStage_inv_hom_id p A P I γ J hIJ E hE e hstable EStage hEStage

section EnvelopeStageTower

variable (EStage : ∀ e : ℕ, envelopeStage p A P I γ J hIJ e)
variable (hEStage : ∀ e : ℕ,
  DividedPowerEnvelope.IsUniversal γ (stageMap p A P e)
    (stageIdeal_contains_base p A P I J hIJ e) (EStage e))

/-- The presentation of a lower envelope stage annihilates every higher power of `p`. -/
theorem envelopeStageTransition_ker (higher lower : ℕ) (hle : lower ≤ higher) :
    Ideal.span {((p : P) ^ higher)} ≤
      RingHom.ker (envelopeStageFromP p lower (EStage lower)) := sorry

/-- The presentation of a higher finite quotient in a lower envelope stage. -/
noncomputable def envelopeStageTransitionPresentation
    (higher lower : ℕ) (hle : lower ≤ higher) :
    quotient p P higher →+* (EStage lower).D :=
  Ideal.Quotient.lift _
    (envelopeStageFromP p lower (EStage lower))
    (envelopeStageTransition_ker p A P I γ J hIJ EStage higher lower hle)

/-- The transition presentation respects the divided powers of the base. -/
theorem envelopeStageTransitionPresentation_isDPMorphism
    (higher lower : ℕ) (hle : lower ≤ higher) :
    DividedPowers.IsDPMorphism γ (EStage lower).D.dividedPowers
      ((envelopeStageTransitionPresentation p A P I γ J hIJ EStage
        higher lower hle).comp (stageMap p A P higher)) := sorry

/-- The transition presentation carries the higher presentation ideal into the lower ideal. -/
theorem envelopeStageTransitionPresentation_ideal
    (higher lower : ℕ) (hle : lower ≤ higher) :
    Ideal.map
      (envelopeStageTransitionPresentation p A P I γ J hIJ EStage higher lower hle)
      (stageIdeal p P J higher) ≤ (EStage lower).D.ideal := sorry

/-- The canonical finite-envelope transition, induced by the quotient of presentations. -/
noncomputable def envelopeStageTransition
    (higher lower : ℕ) (hle : lower ≤ higher) :
    (EStage higher).D ⟶ (EStage lower).D :=
  Classical.choose (ExistsUnique.exists
    (hEStage higher
      (envelopeStageTransitionPresentation p A P I γ J hIJ EStage higher lower hle)
      (envelopeStageTransitionPresentation_isDPMorphism p A P I γ J hIJ EStage
        higher lower hle)
      (envelopeStageTransitionPresentation_ideal p A P I γ J hIJ EStage
        higher lower hle)))

/-- The finite-envelope transition is the lift of the quotient presentation. -/
theorem envelopeStageTransition_comp
    (higher lower : ℕ) (hle : lower ≤ higher) :
    (envelopeStageTransition p A P I γ J hIJ EStage hEStage
      higher lower hle).toRingHom.comp (EStage higher).toD =
        envelopeStageTransitionPresentation p A P I γ J hIJ EStage
          higher lower hle := sorry

/-- The inverse system of the specified finite envelopes on the tail starting at `N`. -/
noncomputable def envelopeStageDiagram (N : ℕ) : ℕᵒᵖ ⥤ DividedPowerRing :=
  @Functor.ofOpSequence DividedPowerRing _ (fun e ↦ (EStage (e + N)).D) (fun e ↦
    envelopeStageTransition p A P I γ J hIJ EStage hEStage
      ((e + 1) + N) (e + N) (Nat.add_le_add_right (Nat.le_add_right e 1) N))

/-- The inverse-system successor map is the canonical transition between finite envelopes. -/
theorem envelopeStageDiagram_step (N e : ℕ) :
    (envelopeStageDiagram p A P I γ J hIJ EStage hEStage N).map
      (CategoryTheory.homOfLE (Nat.le_add_right e 1)).op =
        envelopeStageTransition p A P I γ J hIJ EStage hEStage
          ((e + 1) + N) (e + N) (Nat.add_le_add_right (Nat.le_add_right e 1) N) := sorry

variable (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
variable (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A P) hIJ E)
variable (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
variable (hstablePow : IsStableUnderPowers E.D.dividedPowers
  (Ideal.span {(p : E.D)}) N)

/-- The canonical identification of a quotient-power stage with its finite envelope. -/
noncomputable def quotientTowerStageIsoEnvelopeStage (e : ℕ) :
    (DividedPowers.QuotientPowerTower.diagram E.D.dividedPowers
      (Ideal.span {(p : E.D)}) N hstablePow).obj (op e) ≅ (EStage (e + N)).D :=
  (quotientTowerStageIsoEnvelopeQuotient p A P I γ J hIJ E N hN hstablePow e
    (hstablePow e)) ≪≫
      envelopeQuotientIsoStage p A P I γ J hIJ E hE (e + N)
        (hstablePow e) (EStage (e + N)) (hEStage (e + N))

/-- Quotient-stage identifications commute with the canonical finite-envelope transitions. -/
theorem quotientTowerStageIsoEnvelopeStage_naturality
    {index next : ℕᵒᵖ} (arrow : index ⟶ next) :
    (DividedPowers.QuotientPowerTower.diagram E.D.dividedPowers
        (Ideal.span {(p : E.D)}) N hstablePow).map arrow ≫
      (quotientTowerStageIsoEnvelopeStage p A P I γ J hIJ EStage hEStage
        E hE N hN hstablePow next.unop).hom =
      (quotientTowerStageIsoEnvelopeStage p A P I γ J hIJ EStage hEStage
        E hE N hN hstablePow index.unop).hom ≫
        (envelopeStageDiagram p A P I γ J hIJ EStage hEStage N).map arrow := sorry

/-- The quotient-power tower and the specified finite-envelope tower are naturally isomorphic. -/
noncomputable def envelopeStageComparison :
    DividedPowers.QuotientPowerTower.diagram E.D.dividedPowers
      (Ideal.span {(p : E.D)}) N hstablePow ≅
        envelopeStageDiagram p A P I γ J hIJ EStage hEStage N :=
  NatIso.ofComponents
    (fun index ↦ quotientTowerStageIsoEnvelopeStage p A P I γ J hIJ EStage hEStage
      E hE N hN hstablePow index.unop)
    (fun arrow ↦ quotientTowerStageIsoEnvelopeStage_naturality p A P I γ J hIJ
      EStage hEStage E hE N hN hstablePow arrow)

/-- The natural comparison at a stage is the canonical divided-power quotient identification. -/
theorem envelopeStageComparison_hom_app (e : ℕ) :
    (envelopeStageComparison p A P I γ J hIJ EStage hEStage
      E hE N hN hstablePow).hom.app (op e) =
        (quotientTowerStageIsoEnvelopeStage p A P I γ J hIJ EStage hEStage
          E hE N hN hstablePow e).hom := sorry

variable (γhat : DividedPowers (RingHom.ker
  (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN)))
variable (hγhat : DividedPowers.IsDPMorphism E.D.dividedPowers γhat
  (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D)))

/-- The canonical completion cone over the actual finite-envelope inverse system. -/
noncomputable def envelopeStageCompletionCone :
    Cone (envelopeStageDiagram p A P I γ J hIJ EStage hEStage N) where
  pt := envelopeCompletionRing p A P I γ J hIJ E N hN γhat
  π := (DividedPowers.QuotientPowerTower.cone E.D.dividedPowers
      (Ideal.span {(p : E.D)}) N hstablePow hN γhat hγhat).π ≫
    (envelopeStageComparison p A P I γ J hIJ EStage hEStage
      E hE N hN hstablePow).hom

/-- The completion cone leg is adic evaluation followed by the finite-envelope comparison. -/
theorem envelopeStageCompletionCone_π_app (e : ℕ) :
    (envelopeStageCompletionCone p A P I γ J hIJ EStage hEStage
      E hE N hN hstablePow γhat hγhat).π.app (op e) =
        DividedPowers.QuotientPowerTower.leg E.D.dividedPowers
          (Ideal.span {(p : E.D)}) N hstablePow hN γhat hγhat e ≫
            (quotientTowerStageIsoEnvelopeStage p A P I γ J hIJ EStage hEStage
              E hE N hN hstablePow e).hom := sorry

end EnvelopeStageTower

end DividedPowers.PAdic
