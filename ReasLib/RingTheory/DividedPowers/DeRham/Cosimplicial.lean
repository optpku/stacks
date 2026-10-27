/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.MvPolynomial.TensorPower
public import ReasLib.RingTheory.DividedPowers.Envelope.Universal
public import ReasLib.RingTheory.Kaehler.DeRham.DividedPowers
public import ReasLib.Algebra.Category.ModuleCat.Cosimplicial.AdicCompletion
public import ReasLib.Algebra.Category.ModuleCat.Cosimplicial.Homotopy.Operations
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Nilpotent.Defs

@[expose] public section

open CategoryTheory Opposite KaehlerDifferential.DeRham

noncomputable section

universe u

variable {A : Type u} [CommRing A]
variable (p : ℕ) [pPrime : Fact (Nat.Prime p)]
variable [baseLocal : Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable (I : Ideal A) (γ : DividedPowers I)
variable {C : Type u} [CommRing C] [Algebra A C]
variable {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C)
variable (hπ : Function.Surjective π)
variable (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C))
variable (hpnil : IsNilpotent (p : C))
variable (J : (n : ℕ) → Ideal (MvPolynomial.TensorPower.carrier A ι n))
variable (hJ : ∀ n, J n = RingHom.ker (MvPolynomial.TensorPower.diagonal A ι π n).toRingHom)
variable (hIJ : ∀ n, Ideal.map (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) I ≤ J n)
variable (E : (n : ℕ) →
    DividedPowerEnvelope I γ (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) (J n) (hIJ n))
variable (hE : ∀ n,
    DividedPowerEnvelope.IsUniversal γ
      (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) (hIJ n) (E n))

namespace Crystalline

/-- The base map into the principal-adic completion of an envelope. -/
def dnBaseMap (n : ℕ) :
    A →+* AdicCompletion (Ideal.span {(p : (E n).D)}) (E n).D :=
  (algebraMap (E n).D (AdicCompletion (Ideal.span {(p : (E n).D)}) (E n).D)).comp
    ((E n).toD.comp (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)))

/-- The principal-adic completion of an envelope as an algebra over the base. -/
def dn (n : ℕ) : CommAlgCat.{u} A :=
  @CommAlgCat.of A _ (AdicCompletion (Ideal.span {(p : (E n).D)}) (E n).D) _
    (dnBaseMap p I γ J hIJ E n).toAlgebra

/-- The ideal in a completed envelope induced by the envelope ideal. -/
def dnIdeal (n : ℕ) : Ideal (dn p I γ J hIJ E n) :=
  Ideal.map (algebraMap (E n).D (AdicCompletion (Ideal.span {(p : (E n).D)}) (E n).D)) (E n).D.ideal

variable (γbar : (n : ℕ) → DividedPowers (dnIdeal p I γ J hIJ E n))

/-- Tensor reindexing respects the base divided powers of the target envelope. -/
theorem reindex_base {n m : SimplexCategory} (σ : n ⟶ m) :
    DividedPowers.IsDPMorphism γ (E m.len).D.dividedPowers
      (((E m.len).toD.comp
        (MvPolynomial.TensorPower.reindex A ι n.len m.len (SimplexCategory.Hom.toOrderHom σ)).toRingHom).comp
          (algebraMap A (MvPolynomial.TensorPower.carrier A ι n.len))) := by
  have hbase :
      (((E m.len).toD.comp
        (MvPolynomial.TensorPower.reindex A ι n.len m.len
          (SimplexCategory.Hom.toOrderHom σ)).toRingHom).comp
        (algebraMap A (MvPolynomial.TensorPower.carrier A ι n.len))) =
      (E m.len).base.toRingHom := by
    ext a
    exact (congrArg (E m.len).toD
      ((MvPolynomial.TensorPower.reindex A ι n.len m.len
        (SimplexCategory.Hom.toOrderHom σ)).commutes a)).trans
      (RingHom.congr_fun (E m.len).base_toD a).symm
  rw [hbase]
  exact (E m.len).base.isDPMorphism

include hJ in
/-- Tensor reindexing sends the presentation kernel into the target envelope ideal. -/
theorem reindex_ideal {n m : SimplexCategory} (σ : n ⟶ m) :
    Ideal.map ((E m.len).toD.comp
      (MvPolynomial.TensorPower.reindex A ι n.len m.len (SimplexCategory.Hom.toOrderHom σ)).toRingHom)
      (J n.len) ≤ (E m.len).D.ideal := by
  classical
  have hslot {R : Type u} [CommRing R] [Algebra A R] (r : ℕ)
      (f : Fin (r + 1) → MvPolynomial ι A →ₐ[A] R)
      (j : Fin (r + 1)) (x : MvPolynomial ι A) :
      MvPolynomial.TensorPower.liftSlots A ι r f
        (MvPolynomial.TensorPower.slot A ι r j x) = f j x := by
    change PiTensorProduct.lift (MvPolynomial.TensorPower.liftMap A ι r f)
      (PiTensorProduct.tprod A (Pi.mulSingle j x)) = f j x
    rw [PiTensorProduct.lift.tprod]
    change (∏ k, f k ((Pi.mulSingle j x : Fin (r + 1) → MvPolynomial ι A) k)) = f j x
    rw [Finset.prod_eq_single j]
    · simp
    · intro k _ hkj
      simp [Pi.mulSingle, hkj]
    · simp
  have hdiagonal :
      (MvPolynomial.TensorPower.diagonal A ι π m.len).comp
          (MvPolynomial.TensorPower.reindex A ι n.len m.len
            (SimplexCategory.Hom.toOrderHom σ)) =
        MvPolynomial.TensorPower.diagonal A ι π n.len := by
    apply PiTensorProduct.algHom_ext
    intro j
    apply AlgHom.ext
    intro x
    change MvPolynomial.TensorPower.diagonal A ι π m.len
        (MvPolynomial.TensorPower.reindex A ι n.len m.len
          (SimplexCategory.Hom.toOrderHom σ) (MvPolynomial.TensorPower.slot A ι n.len j x)) =
      MvPolynomial.TensorPower.diagonal A ι π n.len (MvPolynomial.TensorPower.slot A ι n.len j x)
    simp only [MvPolynomial.TensorPower.diagonal, MvPolynomial.TensorPower.reindex, hslot]
  apply Ideal.map_le_iff_le_comap.mpr
  intro x hx
  have hx0 : MvPolynomial.TensorPower.diagonal A ι π n.len x = 0 := by
    simpa [hJ n.len] using hx
  have hreindex : MvPolynomial.TensorPower.reindex A ι n.len m.len
      (SimplexCategory.Hom.toOrderHom σ) x ∈ J m.len := by
    rw [hJ m.len, RingHom.mem_ker]
    exact (DFunLike.congr_fun hdiagonal x).trans hx0
  exact (E m.len).ideal_map (Ideal.mem_map_of_mem (E m.len).toD hreindex)

/-- The unique divided-power lift of tensor reindexing through the universal envelope. -/
def envelopeHom {n m : SimplexCategory} (σ : n ⟶ m) :
    (E n.len).D ⟶ (E m.len).D :=
  (hE n.len
    ((E m.len).toD.comp
      (MvPolynomial.TensorPower.reindex A ι n.len m.len (SimplexCategory.Hom.toOrderHom σ)).toRingHom)
    (reindex_base I γ J hIJ E σ)
    (reindex_ideal I γ π J hJ hIJ E σ)).choose

/-- The envelope lift agrees with tensor reindexing on the presentation. -/
theorem envelopeHom_comp_toD {n m : SimplexCategory} (σ : n ⟶ m) :
    (envelopeHom I γ π J hJ hIJ E hE σ).toRingHom.comp (E n.len).toD =
      (E m.len).toD.comp
        (MvPolynomial.TensorPower.reindex A ι n.len m.len (SimplexCategory.Hom.toOrderHom σ)).toRingHom := by
  exact (hE n.len
    ((E m.len).toD.comp
      (MvPolynomial.TensorPower.reindex A ι n.len m.len (SimplexCategory.Hom.toOrderHom σ)).toRingHom)
    (reindex_base I γ J hIJ E σ)
    (reindex_ideal I γ π J hJ hIJ E σ)).choose_spec.1

/-- Every power of the principal ideal is preserved by the envelope lift. -/
theorem dnHom_ideal {n m : SimplexCategory} (σ : n ⟶ m) (degree : ℕ) :
    Ideal.span {(p : (E n.len).D)} ^ degree ≤
      (Ideal.span {(p : (E m.len).D)} ^ degree).comap
        (envelopeHom I γ π J hJ hIJ E hE σ).toRingHom := sorry

/-- The quotient coordinates of the completed envelope lift are compatible. -/
theorem dnHom_compatible {n m : SimplexCategory} (σ : n ⟶ m)
    {lower upper : ℕ} (h : lower ≤ upper) :
    (Ideal.Quotient.factorPow (Ideal.span {(p : (E m.len).D)}) h).comp
      ((Ideal.quotientMap (Ideal.span {(p : (E m.len).D)} ^ upper)
          (envelopeHom I γ π J hJ hIJ E hE σ).toRingHom
          (dnHom_ideal p I γ π J hJ hIJ E hE σ upper)).comp
        (AdicCompletion.evalₐ (Ideal.span {(p : (E n.len).D)}) upper).toRingHom) =
      (Ideal.quotientMap (Ideal.span {(p : (E m.len).D)} ^ lower)
          (envelopeHom I γ π J hJ hIJ E hE σ).toRingHom
          (dnHom_ideal p I γ π J hJ hIJ E hE σ lower)).comp
        (AdicCompletion.evalₐ (Ideal.span {(p : (E n.len).D)}) lower).toRingHom := sorry

/-- Completion of the envelope lift through its compatible ring-quotient maps. -/
def dnHom {n m : SimplexCategory} (σ : n ⟶ m) :
    dn p I γ J hIJ E n.len →+* dn p I γ J hIJ E m.len :=
  AdicCompletion.liftRingHom (Ideal.span {(p : (E m.len).D)})
    (fun degree ↦
      (Ideal.quotientMap (Ideal.span {(p : (E m.len).D)} ^ degree)
          (envelopeHom I γ π J hJ hIJ E hE σ).toRingHom
          (dnHom_ideal p I γ π J hJ hIJ E hE σ degree)).comp
        (AdicCompletion.evalₐ (Ideal.span {(p : (E n.len).D)}) degree).toRingHom)
    (fun h ↦ dnHom_compatible p I γ π J hJ hIJ E hE σ h)

/-- The completed lift extends the universal envelope morphism. -/
theorem dnHom_comp_completion {n m : SimplexCategory} (σ : n ⟶ m) :
    (dnHom p I γ π J hJ hIJ E hE σ).comp
        (algebraMap (E n.len).D (AdicCompletion (Ideal.span {(p : (E n.len).D)}) (E n.len).D)) =
      (algebraMap (E m.len).D (AdicCompletion (Ideal.span {(p : (E m.len).D)}) (E m.len).D)).comp
        (envelopeHom I γ π J hJ hIJ E hE σ).toRingHom := sorry

/-- The completed lift is compatible with the relative base maps. -/
theorem dnHom_comp_base {n m : SimplexCategory} (σ : n ⟶ m) :
    (dnHom p I γ π J hJ hIJ E hE σ).comp
        (dnBaseMap p I γ J hIJ E n.len) =
      dnBaseMap p I γ J hIJ E m.len := sorry

variable (hγbar : ∀ n, DividedPowers.IsDPMorphism (E n).D.dividedPowers (γbar n)
  (algebraMap (E n).D (AdicCompletion (Ideal.span {(p : (E n).D)}) (E n).D)))

include hγbar in
/-- The induced completed divided powers are preserved by completed simplex maps. -/
theorem dnHom_isDPMorphism {n m : SimplexCategory} (σ : n ⟶ m) :
    DividedPowers.IsDPMorphism (γbar n.len) (γbar m.len)
      (dnHom p I γ π J hJ hIJ E hE σ) := sorry

/-- The completed envelope map for an identity is the identity ring morphism. -/
theorem dnHom_id (n : SimplexCategory) :
    CommRingCat.ofHom (dnHom p I γ π J hJ hIJ E hE (𝟙 n)) =
      𝟙 (CommRingCat.of (dn p I γ J hIJ E n.len)) := sorry

/-- Completed envelope maps preserve composition of simplex operators. -/
theorem dnHom_comp {n m k : SimplexCategory} (σ : n ⟶ m) (τ : m ⟶ k) :
    CommRingCat.ofHom (dnHom p I γ π J hJ hIJ E hE (σ ≫ τ)) =
      CommRingCat.ofHom (dnHom p I γ π J hJ hIJ E hE σ) ≫
        CommRingCat.ofHom (dnHom p I γ π J hJ hIJ E hE τ) := sorry

/-- The cosimplicial ring of completed envelopes, with universal-property-induced maps. -/
def dStar : CosimplicialObject CommRingCat.{u} where
  obj degree := CommRingCat.of
    (dn p I γ J hIJ E degree.len)
  map σ := CommRingCat.ofHom (dnHom p I γ π J hJ hIJ E hE σ)
  map_id := dnHom_id p I γ π J hJ hIJ E hE
  map_comp := dnHom_comp p I γ π J hJ hIJ E hE

/-- The completed envelope diagram has the prescribed rings in every degree. -/
theorem dStar_obj (degree : ℕ) :
    (dStar p I γ π J hJ hIJ E hE).obj (SimplexCategory.mk degree) =
      CommRingCat.of
        (dn p I γ J hIJ E degree) := rfl

/-- The uncompleted relative divided-power differential module in one degree. -/
def omegaModule (degree : ℕ) :
    ModuleCat.{u}
      (dn p I γ J hIJ E degree) :=
  ModuleCat.of
    (AdicCompletion (Ideal.span {(p : (E degree).D)}) (E degree).D)
    (dividedPowerDifferential
      (dnBaseMap p I γ J hIJ E degree) (γbar degree))

omit pPrime baseLocal in
/-- The differential module is the quotient by the relative divided-power relations. -/
theorem omegaModule_eq (degree : ℕ) :
    omegaModule p I γ J hIJ E γbar degree =
      ModuleCat.of
        (AdicCompletion (Ideal.span {(p : (E degree).D)}) (E degree).D)
        (dividedPowerDifferential
          (dnBaseMap p I γ J hIJ E degree) (γbar degree)) := rfl

/-- The Kähler differential comparison followed by the target divided-power quotient. -/
def omegaKaehlerMap {n m : SimplexCategory} (σ : n ⟶ m) :
    ModuleCat.of
        (dn p I γ J hIJ E n.len)
        (KaehlerDifferential A
          (dn p I γ J hIJ E n.len)) ⟶
      (ModuleCat.restrictScalars (dnHom p I γ π J hJ hIJ E hE σ)).obj
        (omegaModule p I γ J hIJ E γbar m.len) :=
  let source := dn p I γ J hIJ E n.len
  let target := dn p I γ J hIJ E m.len
  let baseTarget := dnBaseMap p I γ J hIJ E m.len
  let ringMap := dnHom p I γ π J hJ hIJ E hE σ
  -- Local instance justification (noncanonical choice): the simplex operator selects the scalar map between these two completed rings.
  letI : Algebra source target := ringMap.toAlgebra
  -- Local instance justification (defeq pin): the Kähler map uses restriction along this simplex operator, matching its ModuleCat codomain.
  letI : Module source (KaehlerDifferential A target) := Module.compHom _ ringMap
  -- Local instance justification (defeq pin): the scalar tower is the base-compatible completed simplex map, not an independent algebra structure.
  letI : IsScalarTower A source target :=
    IsScalarTower.of_algebraMap_eq'
      (dnHom_comp_base p I γ π J hJ hIJ E hE σ).symm
  ModuleCat.ofHom (KaehlerDifferential.map A A source target) ≫
    (ModuleCat.restrictScalars ringMap).map
      (ModuleCat.ofHom
        (R := AdicCompletion (Ideal.span {(p : (E m.len).D)}) (E m.len).D)
        (dividedPowerRelations baseTarget (γbar m.len)).mkQ)

/-- The Kähler comparison sends universal differentials to target differentials. -/
theorem omegaKaehlerMap_D {n m : SimplexCategory} (σ : n ⟶ m)
    (element : dn p I γ J hIJ E n.len) :
    omegaKaehlerMap p I γ π J hJ hIJ E hE γbar σ
        (KaehlerDifferential.D A
          (dn p I γ J hIJ E n.len) element) =
      dividedPowerDifferentialDerivation
        (dnBaseMap p I γ J hIJ E m.len) (γbar m.len)
        (dnHom p I γ π J hJ hIJ E hE σ element) := sorry

/-- Divided-power compatibility makes the Kähler comparison kill the source relations. -/
theorem relations_le_ker {n m : SimplexCategory} (σ : n ⟶ m)
    (hσ : DividedPowers.IsDPMorphism (γbar n.len) (γbar m.len)
      (dnHom p I γ π J hJ hIJ E hE σ)) :
    dividedPowerRelations
        (dnBaseMap p I γ J hIJ E n.len) (γbar n.len) ≤
      LinearMap.ker (omegaKaehlerMap p I γ π J hJ hIJ E hE γbar σ).hom := sorry

/-- Descent of the differential comparison through the source relation quotient. -/
def omegaHom {n m : SimplexCategory} (σ : n ⟶ m) :
    omegaModule p I γ J hIJ E γbar n.len ⟶
      (ModuleCat.restrictScalars (dnHom p I γ π J hJ hIJ E hE σ)).obj
        (omegaModule p I γ J hIJ E γbar m.len) :=
  ModuleCat.homEquiv.symm
    ((dividedPowerRelations
      (dnBaseMap p I γ J hIJ E n.len) (γbar n.len)).liftQ
      (omegaKaehlerMap p I γ π J hJ hIJ E hE γbar σ).hom
      (relations_le_ker p I γ π J hJ hIJ E hE γbar σ
        (dnHom_isDPMorphism p I γ π J hJ hIJ E hE γbar hγbar σ)))

/-- The descended comparison commutes with the quotient of Kähler differentials. -/
theorem omegaHom_mkQ {n m : SimplexCategory} (σ : n ⟶ m)
    (differential : KaehlerDifferential A
      (dn p I γ J hIJ E n.len)) :
    omegaHom p I γ π J hJ hIJ E hE γbar hγbar σ
        ((dividedPowerRelations
          (dnBaseMap p I γ J hIJ E n.len) (γbar n.len)).mkQ differential) =
      omegaKaehlerMap p I γ π J hJ hIJ E hE γbar σ differential := sorry

/-- The differential comparison for an identity is the identity restriction map. -/
theorem omegaHom_id (X : (SimplexCategoryᵒᵖ)ᵒᵖ) :
    omegaHom p I γ π J hJ hIJ E hE γbar hγbar (𝟙 (unop (unop X))) =
      (ModuleCat.restrictScalarsId'
        ((moduleRingPresheaf (dStar p I γ π J hJ hIJ E hE)).map (𝟙 X)).hom
        (congrArg RingCat.Hom.hom
          ((moduleRingPresheaf (dStar p I γ π J hJ hIJ E hE)).map_id X))).inv.app _ := sorry

/-- Differential comparisons compose through the canonical scalar restriction isomorphism. -/
theorem omegaHom_comp {X Y Z : (SimplexCategoryᵒᵖ)ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    omegaHom p I γ π J hJ hIJ E hE γbar hγbar (f ≫ g).unop.unop =
      omegaHom p I γ π J hJ hIJ E hE γbar hγbar f.unop.unop ≫
        (ModuleCat.restrictScalars
          ((moduleRingPresheaf (dStar p I γ π J hJ hIJ E hE)).map f).hom).map
          (omegaHom p I γ π J hJ hIJ E hE γbar hγbar g.unop.unop) ≫
        (ModuleCat.restrictScalarsComp'
          ((moduleRingPresheaf (dStar p I γ π J hJ hIJ E hE)).map f).hom
          ((moduleRingPresheaf (dStar p I γ π J hJ hIJ E hE)).map g).hom
          ((moduleRingPresheaf (dStar p I γ π J hJ hIJ E hE)).map (f ≫ g)).hom
          (congrArg RingCat.Hom.hom
            ((moduleRingPresheaf (dStar p I γ π J hJ hIJ E hE)).map_comp f g))).inv.app _ := sorry

/-- The relative divided-power differential presheaf before module completion. -/
def omegaUncompleted :
    PresheafOfModules.{u} (moduleRingPresheaf (dStar p I γ π J hJ hIJ E hE)) where
  obj degree := omegaModule p I γ J hIJ E γbar
    (unop (unop degree)).len
  map operator := omegaHom p I γ π J hJ hIJ E hE γbar hγbar
    operator.unop.unop
  map_id := omegaHom_id p I γ π J hJ hIJ E hE γbar hγbar
  map_comp := omegaHom_comp p I γ π J hJ hIJ E hE γbar hγbar

/-- Evaluation of the uncompleted differential presheaf recovers the relation quotient. -/
theorem omegaUncompleted_obj (degree : ℕ) :
    (omegaUncompleted p I γ π J hJ hIJ E hE γbar hγbar).obj
        (op (op (SimplexCategory.mk degree))) =
      omegaModule p I γ J hIJ E γbar degree := rfl

/-- Completed simplex maps preserve the principal ideals generated by the prime. -/
theorem primeIdeals_map_mem {n m : SimplexCategory} (σ : n ⟶ m)
    {x : (dStar p I γ π J hJ hIJ E hE).obj n}
    (hx : x ∈ Ideal.span {(p : (dStar p I γ π J hJ hIJ E hE).obj n)}) :
    ((dStar p I γ π J hJ hIJ E hE).map σ).hom x ∈
      Ideal.span {(p : (dStar p I γ π J hJ hIJ E hE).obj m)} := sorry

/-- The degreewise principal ideals generated by `p`, preserved by every ring map. -/
def primeIdeals : CosimplicialIdeal (dStar p I γ π J hJ hIJ E hE) where
  obj degree := Ideal.span {(p : (dStar p I γ π J hJ hIJ E hE).obj degree)}
  map_mem := primeIdeals_map_mem p I γ π J hJ hIJ E hE

/-- The completion ideal in every degree is the principal ideal generated by `p`. -/
theorem primeIdeals_obj (degree : SimplexCategory) :
    (primeIdeals p I γ π J hJ hIJ E hE).obj degree =
      Ideal.span {(p : (dStar p I γ π J hJ hIJ E hE).obj degree)} := rfl

/-- The completed differential diagram, using quotient descent and functorial completion. -/
def omegaDStar :
    PresheafOfModules.{u} (moduleRingPresheaf (dStar p I γ π J hJ hIJ E hE)) :=
  CosimplicialModule.adicCompletion
    (primeIdeals p I γ π J hJ hIJ E hE)
    (omegaUncompleted p I γ π J hJ hIJ E hE γbar hγbar)

/-- Each stage is the principal-adic completion of the relative differential quotient. -/
theorem omegaDStar_obj (degree : ℕ) :
    (omegaDStar p I γ π J hJ hIJ E hE γbar hγbar).obj
        (op (op (SimplexCategory.mk degree))) =
      ModuleCat.of (AdicCompletion (Ideal.span {(p : (E degree).D)}) (E degree).D)
        (AdicCompletion
          (Ideal.span {(p : AdicCompletion (Ideal.span {(p : (E degree).D)}) (E degree).D)})
          (dividedPowerDifferential (dnBaseMap p I γ J hIJ E degree) (γbar degree))) := rfl

end Crystalline

variable (γbar : (n : ℕ) → DividedPowers (Crystalline.dnIdeal p I γ J hIJ E n))

include hπ hIC hpnil baseLocal pPrime in
/-- The completed divided-power differentials of universal polynomial tensor envelopes
are homotopic to zero as a module over their cosimplicial completed ring. -/
theorem crystallineOmegaDStar_homotopic_zero
    (hγbar : ∀ n, DividedPowers.IsDPMorphism (E n).D.dividedPowers (γbar n)
      (algebraMap (E n).D (AdicCompletion (Ideal.span {(p : (E n).D)}) (E n).D))) :
    CosimplicialModule.Homotopic
      (𝟙 (Crystalline.omegaDStar p I γ π J hJ hIJ E hE γbar hγbar))
      (0 :
        Crystalline.omegaDStar p I γ π J hJ hIJ E hE γbar hγbar ⟶
          Crystalline.omegaDStar p I γ π J hJ hIJ E hE γbar hγbar) := sorry
