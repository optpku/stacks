module

public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.Derived.FiniteGeneration
import StacksCheckRecall

/-!
# Lemma 61.28.7

A derived-complete sheaf of `Λ`-modules on the pro-étale site of a weakly
contractible affine scheme, with locally constant finite-type reduction
modulo `I`, is an epimorphic image of a finite coproduct of copies of
`underline(Λ)^∧`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProetaleDerived (constantCoefficientRing)

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme.ProEt

variable {X : Scheme.{u}} {Λ : Type w} [CommRing Λ]
variable [HasWeakSheafify (topology X) (ModuleCat.{w} Λ)]

-- Canonical shape evidence is bound locally to avoid repeated colimit-instance search.
-- This private proof must remain available in the exported coproduct type.
set_option backward.privateInPublic true in
private theorem sourceFiniteDiscreteSheafHasColimit (n : ℕ)
    (D : Discrete (Fin n) ⥤ Sheaf (topology X) (ModuleCat.{w} Λ)) :
    HasColimit D := by
  -- Local instance justification (search instability): Pin canonical additive-group colimits for this finite shape before constructing module colimits, avoiding the previously timing-out generic search.
  letI : HasColimitsOfShape (Discrete (Fin n)) AddCommGrpCat.{w} :=
    AddCommGrpCat.hasColimitsOfShape
  -- Local instance justification (search instability): Pin canonical module colimits for this finite shape before constructing sheaf colimits, avoiding the previously timing-out generic search.
  letI : HasColimitsOfShape (Discrete (Fin n)) (ModuleCat.{w} Λ) :=
    ModuleCat.hasColimitsOfShape (R := Λ) (J := Discrete (Fin n))
  have h : HasColimitsOfShape (Discrete (Fin n))
      (Sheaf (topology X) (ModuleCat.{w} Λ)) :=
    Sheaf.instHasColimitsOfShape
  exact h.has_colimit D

variable [HasWeakSheafify (topology X) CommRingCat.{w}]
variable [HasWeakSheafify (topology X) RingCat.{w}]
variable [HasWeakSheafify (topology X) AddCommGrpCat.{w}]
variable [(topology X).WEqualsLocallyBijective RingCat.{w}]
variable [(topology X).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [(topology X).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [(topology X).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [(topology X).PreservesSheafification (forget₂ CommRingCat.{w} RingCat.{w})]
variable [UnivLE.{u + 1, w}]
variable [LocallySmall
    (SheafOfModules (ringSheafOfComm (constantCoefficientRing X Λ)))]
variable [WellPowered
    (SheafOfModules (ringSheafOfComm (constantCoefficientRing X Λ)))]
variable [∀ U : X.ProEt, HasWeakSheafify ((topology X).over U) (ModuleCat.{w} Λ)]

-- The expected type uses the private proof of canonical colimit existence.
set_option backward.privateInPublic true in
/- Lemma 61.28.7: A derived-complete module sheaf on a weakly contractible affine
scheme with locally constant finite-type reduction is a quotient of a finite
coproduct of completed constant coefficient sheaves. -/
@[stacks 09BZ] #check (AlgebraicGeometry.Scheme.ProEt.exists_epi_from_lambdaHat :
    ∀ [IsAffine X] [IsNoetherianRing Λ]
      [(topology X).IsWeaklyContractible (ProEt.mk (𝟙 X))]
      (I : Ideal Λ) (F : Sheaf (topology X) (ModuleCat.{w} Λ))
      (hF : DerivedComplete.IsDerivedComplete I F)
      (hquot : IsFiniteTypeLocallyConstantModule (IdealPower.quotient I F 1)),
    ∃ t : ℕ,
      -- Local instance justification (search instability): Pin the proved colimit evidence for this exact completed-constant diagram after t is fixed, avoiding the previously timing-out polymorphic instance lookup.
      letI : HasColimit (Discrete.functor (fun _ : Fin t ↦
          ConstantSheaf.AdicCompletion.ofModule (topology X) I (ModuleCat.of Λ Λ))) :=
        sourceFiniteDiscreteSheafHasColimit t (Discrete.functor (fun _ : Fin t ↦
          ConstantSheaf.AdicCompletion.ofModule (topology X) I (ModuleCat.of Λ Λ)))
      ∃ (π : (∐ fun _ : Fin t ↦
          ConstantSheaf.AdicCompletion.ofModule (topology X) I (ModuleCat.of Λ Λ)) ⟶ F),
        Epi π)

end AlgebraicGeometry.Scheme.ProEt
