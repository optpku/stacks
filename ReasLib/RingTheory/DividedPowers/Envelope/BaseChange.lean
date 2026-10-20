module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import ReasLib.Algebra.Category.ModuleCat.Tor.Notation
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import ReasLib.RingTheory.DividedPowers.Envelope.Universal

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct Algebra.TensorProduct.Right

universe u

/-- Under quotient flatness and vanishing of the first Tor group, the universal
divided-power envelope commutes with the corresponding base change. -/
theorem DividedPowerEnvelope.baseChange_of_quotient_flat_of_isZero_tor_one
    {A B B' : Type u} [CommRing A] [CommRing B] [CommRing B']
    [Algebra A B] [Algebra A B'] [Algebra B B'] [IsScalarTower A B B']
    {I : Ideal A} (γ : DividedPowers I) {J : Ideal B}
    (hIJ : Ideal.map (algebraMap A B) I ≤ J)
    (E : DividedPowerEnvelope I γ (algebraMap A B) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A B) hIJ E)
    (hIcomp : Ideal.map (algebraMap A B) I ≤
      (Ideal.map (algebraMap A B') I).comap (algebraMap B B'))
    (hflat : RingHom.Flat
      (Ideal.quotientMap (Ideal.map (algebraMap A B') I)
        (algebraMap B B') hIcomp))
    (htor : IsZero (Tor₁[B](B', B ⧸ Ideal.map (algebraMap A B) I)))
    (hIJ' : Ideal.map (algebraMap A B') I ≤ Ideal.map (algebraMap B B') J)
    (E' : DividedPowerEnvelope I γ (algebraMap A B')
      (Ideal.map (algebraMap B B') J) hIJ')
    (hE' : DividedPowerEnvelope.IsUniversal γ (algebraMap A B') hIJ' E')
    [Algebra B E.D] (hbase : algebraMap B E.D = E.toD)
    [Algebra B' E'.D] (hbase' : algebraMap B' E'.D = E'.toD) :
    Nonempty (TensorProduct B E.D B' ≃ₐ[B'] E'.D) := sorry

namespace DividedPowerEnvelope

/-- The universal divided-power envelope map induced by a homomorphism of
divided-power rings and extension of the envelope ideal. -/
noncomputable def baseChangeDPMorphism
    {B B' : Type u} [CommRing B] [CommRing B'] [Algebra B B']
    {I J : Ideal B} (γ : DividedPowers I)
    (hIJ : Ideal.map (RingHom.id B) I ≤ J)
    (E : DividedPowerEnvelope I γ (RingHom.id B) J hIJ)
    (hE : IsUniversal γ (RingHom.id B) hIJ E)
    {I' J' : Ideal B'} (γ' : DividedPowers I')
    (hγ : DividedPowers.IsDPMorphism γ γ' (algebraMap B B'))
    (hJ' : J' = Ideal.map (algebraMap B B') J + I')
    (hI' : Ideal.map (RingHom.id B') I' ≤ J')
    (E' : DividedPowerEnvelope I' γ' (RingHom.id B') J' hI') : E.D ⟶ E'.D :=
  (hE (E'.toD.comp (algebraMap B B'))
    (Eq.mpr (congrArg (DividedPowers.IsDPMorphism γ E'.D.dividedPowers)
      (RingHom.comp_id (E'.toD.comp (algebraMap B B'))))
      (DividedPowers.IsDPMorphism.comp E'.D.dividedPowers
        (Eq.mp (congrArg (DividedPowers.IsDPMorphism γ' E'.D.dividedPowers)
          (E'.base_toD.trans (RingHom.comp_id E'.toD))) E'.base.isDPMorphism) hγ))
    (le_trans (le_of_eq (Ideal.map_map (algebraMap B B') E'.toD).symm)
      ((Ideal.map_mono (le_trans le_sup_left (le_of_eq hJ'.symm))).trans
        E'.ideal_map))).choose

/-- The induced envelope morphism commutes with the structure map and extends
the given homomorphism of divided-power rings. -/
theorem baseChangeDPMorphism_spec
    {B B' : Type u} [CommRing B] [CommRing B'] [Algebra B B']
    {I J : Ideal B} (γ : DividedPowers I)
    (hIJ : Ideal.map (RingHom.id B) I ≤ J)
    (E : DividedPowerEnvelope I γ (RingHom.id B) J hIJ)
    (hE : IsUniversal γ (RingHom.id B) hIJ E)
    {I' J' : Ideal B'} (γ' : DividedPowers I')
    (hγ : DividedPowers.IsDPMorphism γ γ' (algebraMap B B'))
    (hJ' : J' = Ideal.map (algebraMap B B') J + I')
    (hI' : Ideal.map (RingHom.id B') I' ≤ J')
    (E' : DividedPowerEnvelope I' γ' (RingHom.id B') J' hI') :
    (baseChangeDPMorphism γ hIJ E hE γ' hγ hJ' hI' E').toRingHom.comp E.toD =
      E'.toD.comp (algebraMap B B') ∧
    DividedPowers.DPMorphism.comp
      (baseChangeDPMorphism γ hIJ E hE γ' hγ hJ' hI' E') E.base =
      DividedPowers.DPMorphism.comp E'.base (DividedPowers.DPMorphism.mk' hγ) := sorry

/-- A divided-power envelope morphism extending the base-ring map is uniquely
the morphism induced by the universal mapping property. -/
theorem baseChangeDPMorphism_unique
    {B B' : Type u} [CommRing B] [CommRing B'] [Algebra B B']
    {I J : Ideal B} (γ : DividedPowers I)
    (hIJ : Ideal.map (RingHom.id B) I ≤ J)
    (E : DividedPowerEnvelope I γ (RingHom.id B) J hIJ)
    (hE : IsUniversal γ (RingHom.id B) hIJ E)
    {I' J' : Ideal B'} (γ' : DividedPowers I')
    (hγ : DividedPowers.IsDPMorphism γ γ' (algebraMap B B'))
    (hJ' : J' = Ideal.map (algebraMap B B') J + I')
    (hI' : Ideal.map (RingHom.id B') I' ≤ J')
    (E' : DividedPowerEnvelope I' γ' (RingHom.id B') J' hI')
    (ψ : E.D ⟶ E'.D)
    (hψ : ψ.toRingHom.comp E.toD = E'.toD.comp (algebraMap B B')) :
    ψ = baseChangeDPMorphism γ hIJ E hE γ' hγ hJ' hI' E' := sorry

/-- The canonical base-change algebra map sends a pure tensor to the product
of the induced envelope image and its scalar from the new base ring. -/
noncomputable def baseChangeMap
    {B B' : Type u} [CommRing B] [CommRing B'] [Algebra B B']
    {I J : Ideal B} (γ : DividedPowers I)
    (hIJ : Ideal.map (RingHom.id B) I ≤ J)
    (E : DividedPowerEnvelope I γ (RingHom.id B) J hIJ)
    (hE : IsUniversal γ (RingHom.id B) hIJ E)
    {I' J' : Ideal B'} (γ' : DividedPowers I')
    (hγ : DividedPowers.IsDPMorphism γ γ' (algebraMap B B'))
    (hJ' : J' = Ideal.map (algebraMap B B') J + I')
    (hI' : Ideal.map (RingHom.id B') I' ≤ J')
    (E' : DividedPowerEnvelope I' γ' (RingHom.id B') J' hI')
    [Algebra B E.D] (hbase : algebraMap B E.D = E.toD)
    [Algebra B' E'.D] (hbase' : algebraMap B' E'.D = E'.toD) :
    TensorProduct B E.D B' →ₐ[B'] E'.D :=
  (@Algebra.TensorProduct.liftEquivRight B B' E.D _ _ _ _ _
    E'.D _ (Algebra.restrictScalars B B' E'.D) _ (IsScalarTower.restrictScalars B B' E'.D)
    (@AlgHom.mk B E.D E'.D _ _ _ _ (Algebra.restrictScalars B B' E'.D)
      (baseChangeDPMorphism γ hIJ E hE γ' hγ hJ' hI' E').toRingHom
      (fun scalar =>
        (congrArg (baseChangeDPMorphism γ hIJ E hE γ' hγ hJ' hI' E')
          (RingHom.congr_fun hbase scalar)).trans
          ((RingHom.congr_fun
            (baseChangeDPMorphism_spec γ hIJ E hE γ' hγ hJ' hI' E').1 scalar).trans
            (RingHom.congr_fun hbase' (algebraMap B B' scalar)).symm)))).comp
    (Algebra.TensorProduct.commRight B B' E.D).symm.toAlgHom

/-- A flat map on quotient rings makes the canonical base-change map between
universal divided-power envelopes bijective when the target ideal is the sum
of the extended source ideal and the new divided-power ideal. -/
theorem baseChange
    {B B' : Type u} [CommRing B] [CommRing B'] [Algebra B B']
    {I J : Ideal B} (γ : DividedPowers I)
    (hIJ : Ideal.map (RingHom.id B) I ≤ J)
    (E : DividedPowerEnvelope I γ (RingHom.id B) J hIJ)
    (hE : IsUniversal γ (RingHom.id B) hIJ E)
    {I' J' : Ideal B'} (γ' : DividedPowers I')
    (hγ : DividedPowers.IsDPMorphism γ γ' (algebraMap B B'))
    (hJ' : J' = Ideal.map (algebraMap B B') J + I')
    (hI' : Ideal.map (RingHom.id B') I' ≤ J')
    (E' : DividedPowerEnvelope I' γ' (RingHom.id B') J' hI')
    (hE' : IsUniversal γ' (RingHom.id B') hI' E')
    [Algebra B E.D] (hbase : algebraMap B E.D = E.toD)
    [Algebra B' E'.D] (hbase' : algebraMap B' E'.D = E'.toD)
    (hflat : RingHom.Flat (Ideal.quotientMap I' (algebraMap B B')
      (Ideal.map_le_iff_le_comap.mp hγ.ideal_comp))) :
    Function.Bijective (baseChangeMap γ hIJ E hE γ' hγ hJ' hI' E' hbase hbase') := sorry

end DividedPowerEnvelope
