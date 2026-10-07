module

public import ReasLib.AlgebraicTopology.CosimplicialObject.Abelian
public import ReasLib.AlgebraicTopology.CosimplicialObject.Homotopy.DeltaOne.Relation
public import stacks_project.Chap60.Lemma_60_16_1
public import stacks_project.Chap60.Lemma_60_19_2_Omega
import Mathlib.Tactic.CrossRefAttribute

open CategoryTheory Opposite
open scoped Simplicial

@[expose] public section

noncomputable section

universe u

variable {A : Type u} [CommRing A]
variable (p : ℕ) [Fact (Nat.Prime p)]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable (I : Ideal A) (γ : DividedPowers I)
variable {C : Type u} [CommRing C] [Algebra A C]
variable {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C)
variable (hπ : Function.Surjective π)
variable (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C))
variable (hpnil : IsNilpotent (p : C))
variable (J : (n : ℕ) → Ideal (tensorPowerCarrier A ι n))
variable (hJ : ∀ n, J n = RingHom.ker (tensorPowerAlgHom π n).toRingHom)
variable (hIJ : ∀ n, Ideal.map (algebraMap A (tensorPowerCarrier A ι n)) I ≤ J n)
variable (E : (n : ℕ) →
    DividedPowerEnvelope I γ (algebraMap A (tensorPowerCarrier A ι n)) (J n) (hIJ n))
variable (hE : ∀ n,
    DividedPowerEnvelope.IsUniversal γ
      (algebraMap A (tensorPowerCarrier A ι n)) (hIJ n) (E n))
variable (γbar : (n : ℕ) →
    DividedPowers
      (crystallineDnIdeal p I γ π hπ n hIC hpnil (J n) (hJ n) (hIJ n) (E n) (hE n)))

namespace Crystalline

/-- Tensor reindexing respects the base divided powers of the target envelope. -/
theorem reindex_base {n m : SimplexCategory} (σ : n ⟶ m) :
    DividedPowers.IsDPMorphism γ (E m.len).D.dividedPowers
      (((E m.len).toD.comp
        (tensorPowerReindex A ι n.len m.len (SimplexCategory.Hom.toOrderHom σ)).toRingHom).comp
          (algebraMap A (tensorPowerCarrier A ι n.len))) := sorry

include hJ in
/-- Tensor reindexing sends the presentation kernel into the target envelope ideal. -/
theorem reindex_ideal {n m : SimplexCategory} (σ : n ⟶ m) :
    Ideal.map ((E m.len).toD.comp
      (tensorPowerReindex A ι n.len m.len (SimplexCategory.Hom.toOrderHom σ)).toRingHom)
      (J n.len) ≤ (E m.len).D.ideal := sorry

/-- The unique divided-power lift of tensor reindexing through the universal envelope. -/
def envelopeHom {n m : SimplexCategory} (σ : n ⟶ m) :
    (E n.len).D ⟶ (E m.len).D :=
  (hE n.len
    ((E m.len).toD.comp
      (tensorPowerReindex A ι n.len m.len (SimplexCategory.Hom.toOrderHom σ)).toRingHom)
    (reindex_base I γ J hIJ E σ)
    (reindex_ideal I γ π J hJ hIJ E σ)).choose

/-- The envelope lift agrees with tensor reindexing on the presentation. -/
theorem envelopeHom_comp_toD {n m : SimplexCategory} (σ : n ⟶ m) :
    (envelopeHom I γ π J hJ hIJ E hE σ).toRingHom.comp (E n.len).toD =
      (E m.len).toD.comp
        (tensorPowerReindex A ι n.len m.len (SimplexCategory.Hom.toOrderHom σ)).toRingHom := sorry

/-- Completion of the universal envelope lift, by its compatible maps on ring quotients. -/
def dnHom {n m : SimplexCategory} (σ : n ⟶ m) :
    crystallineDn p I γ π hπ n.len hIC hpnil (J n.len) (hJ n.len) (hIJ n.len)
        (E n.len) (hE n.len) →+*
      crystallineDn p I γ π hπ m.len hIC hpnil (J m.len) (hJ m.len) (hIJ m.len)
        (E m.len) (hE m.len) :=
  AdicCompletion.liftRingHom (Ideal.span {(p : (E m.len).D)})
    (fun degree ↦
      (Ideal.quotientMap (Ideal.span {(p : (E m.len).D)} ^ degree)
          (envelopeHom I γ π J hJ hIJ E hE σ).toRingHom sorry).comp
        (AdicCompletion.evalₐ (Ideal.span {(p : (E n.len).D)}) degree).toRingHom)
    sorry

/-- The completed lift extends the universal envelope morphism. -/
theorem dnHom_comp_completion {n m : SimplexCategory} (σ : n ⟶ m) :
    (dnHom p I γ π hπ hIC hpnil J hJ hIJ E hE σ).comp
        (algebraMap (E n.len).D
          (crystallineDn p I γ π hπ n.len hIC hpnil (J n.len) (hJ n.len) (hIJ n.len)
            (E n.len) (hE n.len))) =
      (algebraMap (E m.len).D
        (crystallineDn p I γ π hπ m.len hIC hpnil (J m.len) (hJ m.len) (hIJ m.len)
          (E m.len) (hE m.len))).comp
        (envelopeHom I γ π J hJ hIJ E hE σ).toRingHom := sorry

/-- The completed lift is compatible with the relative base maps. -/
theorem dnHom_comp_base {n m : SimplexCategory} (σ : n ⟶ m) :
    (dnHom p I γ π hπ hIC hpnil J hJ hIJ E hE σ).comp
        (crystallineDnBaseMap p I γ π hπ n.len hIC hpnil (J n.len) (hJ n.len) (hIJ n.len)
          (E n.len) (hE n.len)) =
      crystallineDnBaseMap p I γ π hπ m.len hIC hpnil (J m.len) (hJ m.len) (hIJ m.len)
        (E m.len) (hE m.len) := sorry

variable (hγbar : ∀ n, DividedPowers.IsDPMorphism (E n).D.dividedPowers (γbar n)
  (algebraMap (E n).D
    (crystallineDn p I γ π hπ n hIC hpnil (J n) (hJ n) (hIJ n) (E n) (hE n))))

include hγbar in
/-- The induced completed divided powers are preserved by completed simplex maps. -/
theorem dnHom_isDPMorphism {n m : SimplexCategory} (σ : n ⟶ m) :
    DividedPowers.IsDPMorphism (γbar n.len) (γbar m.len)
      (dnHom p I γ π hπ hIC hpnil J hJ hIJ E hE σ) := sorry

/-- The cosimplicial ring of completed envelopes, with universal-property-induced maps. -/
def dStar : CosimplicialObject CommRingCat.{u} where
  obj degree := CommRingCat.of
    (crystallineDn p I γ π hπ degree.len hIC hpnil (J degree.len) (hJ degree.len)
      (hIJ degree.len) (E degree.len) (hE degree.len))
  map σ := CommRingCat.ofHom (dnHom p I γ π hπ hIC hpnil J hJ hIJ E hE σ)
  map_id := sorry
  map_comp := sorry

/-- The completed envelope diagram has the prescribed rings in every degree. -/
theorem dStar_obj (degree : ℕ) :
    (dStar p I γ π hπ hIC hpnil J hJ hIJ E hE).obj (SimplexCategory.mk degree) =
      CommRingCat.of
        (crystallineDn p I γ π hπ degree hIC hpnil (J degree) (hJ degree) (hIJ degree)
          (E degree) (hE degree)) := sorry

/-- The uncompleted relative divided-power differential module in one degree. -/
def omegaModule (degree : ℕ) :
    ModuleCat.{u}
      (crystallineDn p I γ π hπ degree hIC hpnil (J degree) (hJ degree) (hIJ degree)
        (E degree) (hE degree)) :=
  ModuleCat.of
    (crystallineDn p I γ π hπ degree hIC hpnil (J degree) (hJ degree) (hIJ degree)
      (E degree) (hE degree))
    (dividedPowerDifferential
      (crystallineDnBaseMap p I γ π hπ degree hIC hpnil (J degree) (hJ degree)
        (hIJ degree) (E degree) (hE degree)) (γbar degree))

/-- The differential module is the quotient by the relative divided-power relations. -/
theorem omegaModule_eq (degree : ℕ) :
    omegaModule p I γ π hπ hIC hpnil J hJ hIJ E hE γbar degree =
      ModuleCat.of
        (crystallineDn p I γ π hπ degree hIC hpnil (J degree) (hJ degree) (hIJ degree)
          (E degree) (hE degree))
        (dividedPowerDifferential
          (crystallineDnBaseMap p I γ π hπ degree hIC hpnil (J degree) (hJ degree)
            (hIJ degree) (E degree) (hE degree)) (γbar degree)) := sorry

/-- The Kähler differential comparison followed by the target divided-power quotient. -/
def omegaKaehlerMap {n m : SimplexCategory} (σ : n ⟶ m) :
    ModuleCat.of
        (crystallineDn p I γ π hπ n.len hIC hpnil (J n.len) (hJ n.len) (hIJ n.len)
          (E n.len) (hE n.len))
        (KaehlerDifferential A
          (crystallineDn p I γ π hπ n.len hIC hpnil (J n.len) (hJ n.len) (hIJ n.len)
            (E n.len) (hE n.len))) ⟶
      (ModuleCat.restrictScalars (dnHom p I γ π hπ hIC hpnil J hJ hIJ E hE σ)).obj
        (omegaModule p I γ π hπ hIC hpnil J hJ hIJ E hE γbar m.len) :=
  let source := crystallineDn p I γ π hπ n.len hIC hpnil (J n.len) (hJ n.len)
    (hIJ n.len) (E n.len) (hE n.len)
  let target := crystallineDn p I γ π hπ m.len hIC hpnil (J m.len) (hJ m.len)
    (hIJ m.len) (E m.len) (hE m.len)
  let baseTarget := crystallineDnBaseMap p I γ π hπ m.len hIC hpnil (J m.len)
    (hJ m.len) (hIJ m.len) (E m.len) (hE m.len)
  let ringMap := dnHom p I γ π hπ hIC hpnil J hJ hIJ E hE σ
  -- Local instance justification (noncanonical choice): the simplex operator selects the scalar map between these two completed rings.
  letI : Algebra source target := ringMap.toAlgebra
  -- Local instance justification (defeq pin): the Kähler map uses restriction along this simplex operator, matching its ModuleCat codomain.
  letI : Module source (KaehlerDifferential A target) := Module.compHom _ ringMap
  -- Local instance justification (defeq pin): the scalar tower is the base-compatible completed simplex map, not an independent algebra structure.
  letI : IsScalarTower A source target :=
    IsScalarTower.of_algebraMap_eq'
      (dnHom_comp_base p I γ π hπ hIC hpnil J hJ hIJ E hE σ).symm
  ModuleCat.ofHom (KaehlerDifferential.map A A source target) ≫
    (ModuleCat.restrictScalars ringMap).map
      (ModuleCat.ofHom (dividedPowerRelations baseTarget (γbar m.len)).mkQ)

/-- The Kähler comparison sends universal differentials to target differentials. -/
theorem omegaKaehlerMap_D {n m : SimplexCategory} (σ : n ⟶ m)
    (element : crystallineDn p I γ π hπ n.len hIC hpnil (J n.len) (hJ n.len)
      (hIJ n.len) (E n.len) (hE n.len)) :
    omegaKaehlerMap p I γ π hπ hIC hpnil J hJ hIJ E hE γbar σ
        (KaehlerDifferential.D A
          (crystallineDn p I γ π hπ n.len hIC hpnil (J n.len) (hJ n.len) (hIJ n.len)
            (E n.len) (hE n.len)) element) =
      dividedPowerDifferentialDerivation
        (crystallineDnBaseMap p I γ π hπ m.len hIC hpnil (J m.len) (hJ m.len)
          (hIJ m.len) (E m.len) (hE m.len)) (γbar m.len)
        (dnHom p I γ π hπ hIC hpnil J hJ hIJ E hE σ element) := sorry

/-- Divided-power compatibility makes the Kähler comparison kill the source relations. -/
theorem relations_le_ker {n m : SimplexCategory} (σ : n ⟶ m)
    (hσ : DividedPowers.IsDPMorphism (γbar n.len) (γbar m.len)
      (dnHom p I γ π hπ hIC hpnil J hJ hIJ E hE σ)) :
    dividedPowerRelations
        (crystallineDnBaseMap p I γ π hπ n.len hIC hpnil (J n.len) (hJ n.len)
          (hIJ n.len) (E n.len) (hE n.len)) (γbar n.len) ≤
      LinearMap.ker (omegaKaehlerMap p I γ π hπ hIC hpnil J hJ hIJ E hE γbar σ).hom := sorry

/-- Descent of the differential comparison through the source relation quotient. -/
def omegaHom {n m : SimplexCategory} (σ : n ⟶ m) :
    omegaModule p I γ π hπ hIC hpnil J hJ hIJ E hE γbar n.len ⟶
      (ModuleCat.restrictScalars (dnHom p I γ π hπ hIC hpnil J hJ hIJ E hE σ)).obj
        (omegaModule p I γ π hπ hIC hpnil J hJ hIJ E hE γbar m.len) :=
  ModuleCat.homEquiv.symm
    ((dividedPowerRelations
      (crystallineDnBaseMap p I γ π hπ n.len hIC hpnil (J n.len) (hJ n.len)
        (hIJ n.len) (E n.len) (hE n.len)) (γbar n.len)).liftQ
      (omegaKaehlerMap p I γ π hπ hIC hpnil J hJ hIJ E hE γbar σ).hom
      (relations_le_ker p I γ π hπ hIC hpnil J hJ hIJ E hE γbar σ
        (dnHom_isDPMorphism p I γ π hπ hIC hpnil J hJ hIJ E hE γbar hγbar σ)))

/-- The descended comparison commutes with the quotient of Kähler differentials. -/
theorem omegaHom_mkQ {n m : SimplexCategory} (σ : n ⟶ m)
    (differential : KaehlerDifferential A
      (crystallineDn p I γ π hπ n.len hIC hpnil (J n.len) (hJ n.len) (hIJ n.len)
        (E n.len) (hE n.len))) :
    omegaHom p I γ π hπ hIC hpnil J hJ hIJ E hE γbar hγbar σ
        ((dividedPowerRelations
          (crystallineDnBaseMap p I γ π hπ n.len hIC hpnil (J n.len) (hJ n.len)
            (hIJ n.len) (E n.len) (hE n.len)) (γbar n.len)).mkQ differential) =
      omegaKaehlerMap p I γ π hπ hIC hpnil J hJ hIJ E hE γbar σ differential := sorry

/-- The relative divided-power differential presheaf before module completion. -/
def omegaUncompleted :
    PresheafOfModules.{u} (moduleRingPresheaf (dStar p I γ π hπ hIC hpnil J hJ hIJ E hE)) where
  obj degree := omegaModule p I γ π hπ hIC hpnil J hJ hIJ E hE γbar
    (unop (unop degree)).len
  map operator := omegaHom p I γ π hπ hIC hpnil J hJ hIJ E hE γbar hγbar
    operator.unop.unop
  map_id := sorry
  map_comp := sorry

/-- Evaluation of the uncompleted differential presheaf recovers the relation quotient. -/
theorem omegaUncompleted_obj (degree : ℕ) :
    (omegaUncompleted p I γ π hπ hIC hpnil J hJ hIJ E hE γbar hγbar).obj
        (op (op (SimplexCategory.mk degree))) =
      omegaModule p I γ π hπ hIC hpnil J hJ hIJ E hE γbar degree := sorry

/-- The degreewise principal ideals generated by `p`, preserved by every ring map. -/
def primeIdeals : CosimplicialIdeal (dStar p I γ π hπ hIC hpnil J hJ hIJ E hE) where
  obj degree := Ideal.span {(p : (dStar p I γ π hπ hIC hpnil J hJ hIJ E hE).obj degree)}
  map_mem := sorry

/-- The completion ideal in every degree is the principal ideal generated by `p`. -/
theorem primeIdeals_obj (degree : SimplexCategory) :
    (primeIdeals p I γ π hπ hIC hpnil J hJ hIJ E hE).obj degree =
      Ideal.span {(p : (dStar p I γ π hπ hIC hpnil J hJ hIJ E hE).obj degree)} := sorry

/-- The completed differential diagram, using quotient descent and functorial completion. -/
def omegaDStar :
    PresheafOfModules.{u} (moduleRingPresheaf (dStar p I γ π hπ hIC hpnil J hJ hIJ E hE)) :=
  CosimplicialModule.adicCompletion
    (primeIdeals p I γ π hπ hIC hpnil J hJ hIJ E hE)
    (omegaUncompleted p I γ π hπ hIC hpnil J hJ hIJ E hE γbar hγbar)

/-- The completed diagram has the source's completed relative differential modules as stages. -/
theorem omegaDStar_obj (degree : ℕ) :
    (omegaDStar p I γ π hπ hIC hpnil J hJ hIJ E hE γbar hγbar).obj
        (op (op (SimplexCategory.mk degree))) =
      crystallineOmegaModuleCat p I γ π hπ hIC hpnil J hJ hIJ E hE γbar degree := sorry

end Crystalline

/-- Lemma 60.19.2: with notation as in (60.17.0.5), the `D(*)`-cosimplicial
module with stages `Ω_{D(n)}` and divided powers extending those of the
envelopes is linearly homotopic to zero. -/
@[stacks 07L9]
theorem crystallineOmegaDStar_homotopic_zero
    (hγbar : ∀ n, DividedPowers.IsDPMorphism (E n).D.dividedPowers (γbar n)
      (algebraMap (E n).D
        (crystallineDn p I γ π hπ n hIC hpnil (J n) (hJ n) (hIJ n) (E n) (hE n)))) :
    CosimplicialModule.Homotopic
      (𝟙 (Crystalline.omegaDStar p I γ π hπ hIC hpnil J hJ hIJ E hE γbar hγbar))
      (0 :
        Crystalline.omegaDStar p I γ π hπ hIC hpnil J hJ hIJ E hE γbar hγbar ⟶
          Crystalline.omegaDStar p I γ π hπ hIC hpnil J hJ hIJ E hE γbar hγbar) := sorry
