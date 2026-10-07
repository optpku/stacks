module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.Kaehler.Basic
public import stacks_project.Chap60.Lemma_60_16_1_AdicCompletion
public import stacks_project.Chap60.Lemma_60_17_1_Coprojection
public import stacks_project.Chap60.«60_17_0_5»

@[expose] public section

open CategoryTheory Opposite Function
open SimplexCategory.Hom
open ModuleCat

noncomputable section

universe u

/-- Reindexing of iterated tensor-power stages along a map of simplex indices. -/
def tensorPowerReindex (A : Type u) [CommRing A] (ι : Type u) :
    (n : ℕ) → (m : ℕ) → (Fin (n + 1) → Fin (m + 1)) →
      tensorPowerCarrier A ι n →ₐ[A] tensorPowerCarrier A ι m
  | 0, m, σ => tensorPowerSlot A ι m (σ 0)
  | n + 1, m, σ =>
      let previous := tensorPowerStage A ι n
      -- Local instance justification (defeq pin): recursively stored structures are needed to form the next tensor stage.
      letI : CommRing previous.carrier := previous.commRing
      -- Local instance justification (defeq pin): recursively stored structures are needed to form the next tensor stage.
      letI : Algebra A previous.carrier := previous.algebra
      Algebra.TensorProduct.productMap (tensorPowerSlot A ι m (σ 0))
        (tensorPowerReindex A ι n m (fun i : Fin (n + 1) ↦ σ i.succ))

/-- Degree-zero reindexing is the indicated tensor-power slot. -/
theorem tensorPowerReindex_zero (A : Type u) [CommRing A] (ι : Type u)
    (m : ℕ) (σ : Fin 1 → Fin (m + 1)) :
    tensorPowerReindex A ι 0 m σ = tensorPowerSlot A ι m (σ 0) :=
  rfl

section CrystallineDStar

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

/-- The canonical `A`-algebra structure on each completed envelope ring `D(n)`. -/
instance crystallineDn.algebra (n : ℕ) :
    Algebra A (crystallineDn p I γ π hπ n hIC hpnil (J n) (hJ n) (hIJ n) (E n) (hE n)) :=
  (crystallineDnBaseMap p I γ π hπ n hIC hpnil (J n) (hJ n) (hIJ n) (E n) (hE n)).toAlgebra

/-- Induced map of envelope carriers along a simplex operator, via tensor-power
reindexing and a section of the source quotient map. -/
def crystallineEnvelopeHom
    (J : (k : ℕ) → Ideal (tensorPowerCarrier A ι k))
    (hIJ : ∀ k, Ideal.map (algebraMap A (tensorPowerCarrier A ι k)) I ≤ J k)
    (E : (k : ℕ) →
      DividedPowerEnvelope I γ (algebraMap A (tensorPowerCarrier A ι k)) (J k) (hIJ k))
    {n m : SimplexCategory} (σ : n ⟶ m) :
    (E n.len).D →+* (E m.len).D where
  toFun x :=
    (E m.len).toD
      (tensorPowerReindex A ι n.len m.len (toOrderHom σ)
        (surjInv (f := Ideal.Quotient.mk (J n.len)) Ideal.Quotient.mk_surjective
          ((E n.len).toQuotient x)))
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- The envelope map on the image of `toD` recovers tensor-power reindexing. -/
theorem crystallineEnvelopeHom_comp_toD {n m : SimplexCategory} (σ : n ⟶ m)
    (x : tensorPowerCarrier A ι n.len) :
    crystallineEnvelopeHom I γ J hIJ E σ ((E n.len).toD x) =
      (E m.len).toD (tensorPowerReindex A ι n.len m.len (toOrderHom σ) x) :=
  sorry

/-- Induced map of completed rings `D(n) →+* D(m)` along a simplex operator. -/
def crystallineDnHom {n m : SimplexCategory} (σ : n ⟶ m) :
    crystallineDn p I γ π hπ n.len hIC hpnil (J n.len) (hJ n.len) (hIJ n.len) (E n.len) (hE n.len) →+*
      crystallineDn p I γ π hπ m.len hIC hpnil (J m.len) (hJ m.len) (hIJ m.len) (E m.len) (hE m.len) :=
  AdicCompletion.liftRingHom (Ideal.span {(p : (E m.len).D)})
    (fun k ↦
      (Ideal.quotientMap (Ideal.span {(p : (E m.len).D)} ^ k)
          (crystallineEnvelopeHom I γ J hIJ E σ) sorry).comp
        (AdicCompletion.evalₐ (Ideal.span {(p : (E n.len).D)}) k).toRingHom)
    sorry

/-- Evaluation of the completed ring map is the quotient of the envelope map. -/
theorem crystallineDnHom_eval {n m : SimplexCategory} (σ : n ⟶ m) (k : ℕ)
    (x : crystallineDn p I γ π hπ n.len hIC hpnil (J n.len) (hJ n.len) (hIJ n.len)
      (E n.len) (hE n.len)) :
    AdicCompletion.evalₐ (Ideal.span {(p : (E m.len).D)}) k
        (crystallineDnHom p I γ π hπ hIC hpnil J hJ hIJ E hE σ x) =
      (Ideal.quotientMap (Ideal.span {(p : (E m.len).D)} ^ k)
          (crystallineEnvelopeHom I γ J hIJ E σ) sorry)
        (AdicCompletion.evalₐ (Ideal.span {(p : (E n.len).D)}) k x) :=
  sorry

/-- The cosimplicial commutative ring `D(*)` with stages `D(n)`. -/
def crystallineDStar : CosimplicialObject CommRingCat.{u} where
  obj n :=
    CommRingCat.of
      (crystallineDn p I γ π hπ n.len hIC hpnil (J n.len) (hJ n.len) (hIJ n.len)
        (E n.len) (hE n.len))
  map σ :=
    CommRingCat.ofHom (crystallineDnHom p I γ π hπ hIC hpnil J hJ hIJ E hE σ)
  map_id := sorry
  map_comp := sorry

/-- The degree-`n` object of `D(*)` is the completed envelope ring `D(n)`. -/
theorem crystallineDStar_obj (n : ℕ) :
    (crystallineDStar p I γ π hπ hIC hpnil J hJ hIJ E hE).obj (SimplexCategory.mk n) =
      CommRingCat.of
        (crystallineDn p I γ π hπ n hIC hpnil (J n) (hJ n) (hIJ n) (E n) (hE n)) :=
  rfl

variable (γbar : (n : ℕ) →
    DividedPowers
      (crystallineDnIdeal p I γ π hπ n hIC hpnil (J n) (hJ n) (hIJ n) (E n) (hE n)))

/-- Additive structure on each completed divided-power differential module. -/
instance crystallineOmegaDn.addCommGroup (n : ℕ) :
    AddCommGroup
      (crystallineOmegaDn
        (crystallineDnBaseMap p I γ π hπ n hIC hpnil (J n) (hJ n) (hIJ n) (E n) (hE n))
        p (γbar n)) :=
  inferInstance

/-- Module structure on each completed divided-power differential module. -/
instance crystallineOmegaDn.module (n : ℕ) :
    Module
      (crystallineDn p I γ π hπ n hIC hpnil (J n) (hJ n) (hIJ n) (E n) (hE n))
      (crystallineOmegaDn
        (crystallineDnBaseMap p I γ π hπ n hIC hpnil (J n) (hJ n) (hIJ n) (E n) (hE n))
        p (γbar n)) :=
  inferInstance


/-- The degree-`n` object of `Ω_{D(*)}` as a module over `D(n)`. -/
def crystallineOmegaModuleCat (n : ℕ) :
    ModuleCat.{u}
      (crystallineDn p I γ π hπ n hIC hpnil (J n) (hJ n) (hIJ n) (E n) (hE n)) :=
  ModuleCat.of
    (crystallineDn p I γ π hπ n hIC hpnil (J n) (hJ n) (hIJ n) (E n) (hE n))
    (crystallineOmegaDn
      (crystallineDnBaseMap p I γ π hπ n hIC hpnil (J n) (hJ n) (hIJ n) (E n) (hE n))
      p (γbar n))

/-- The simplex operator is compatible with the base maps `A → D(n)` and `A → D(m)`. -/
theorem crystallineDnHom_comp_base {n m : SimplexCategory} (σ : n ⟶ m) :
    (crystallineDnHom p I γ π hπ hIC hpnil J hJ hIJ E hE σ).comp
        (crystallineDnBaseMap p I γ π hπ n.len hIC hpnil (J n.len) (hJ n.len) (hIJ n.len)
          (E n.len) (hE n.len)) =
      crystallineDnBaseMap p I γ π hπ m.len hIC hpnil (J m.len) (hJ m.len) (hIJ m.len)
        (E m.len) (hE m.len) :=
  sorry

/-- Uncompleted divided-power differential comparison along a simplex operator. -/
def crystallineOmegaUncompletedHom {n m : SimplexCategory} (σ : n ⟶ m) :
    let Dn :=
      crystallineDn p I γ π hπ n.len hIC hpnil (J n.len) (hJ n.len) (hIJ n.len)
        (E n.len) (hE n.len)
    let Dm :=
      crystallineDn p I γ π hπ m.len hIC hpnil (J m.len) (hJ m.len) (hIJ m.len)
        (E m.len) (hE m.len)
    let fn :=
      crystallineDnBaseMap p I γ π hπ n.len hIC hpnil (J n.len) (hJ n.len) (hIJ n.len)
        (E n.len) (hE n.len)
    let fm :=
      crystallineDnBaseMap p I γ π hπ m.len hIC hpnil (J m.len) (hJ m.len) (hIJ m.len)
        (E m.len) (hE m.len)
    -- Local instance justification (instance diamond): f.toAlgebra pins Algebra A D(*) to the source base map.
    letI : Algebra A Dn := fn.toAlgebra
    -- Local instance justification (instance diamond): f.toAlgebra pins Algebra A D(*) to the source base map.
    letI : Algebra A Dm := fm.toAlgebra
    -- Local instance justification (defeq pin): pin Algebra D(n) D(m) to the simplex ring map.
    letI : Algebra Dn Dm :=
      (crystallineDnHom p I γ π hπ hIC hpnil J hJ hIJ E hE σ).toAlgebra
    -- Local instance justification (defeq pin): view Ω_{D(m),γ̄} as a D(n)-module by restriction of scalars.
    letI : Module Dn (dividedPowerDifferential fm (γbar m.len)) :=
      Module.compHom _ (crystallineDnHom p I γ π hπ hIC hpnil J hJ hIJ E hE σ)
    dividedPowerDifferential fn (γbar n.len) →ₗ[Dn]
      dividedPowerDifferential fm (γbar m.len) :=
  let Dn :=
    crystallineDn p I γ π hπ n.len hIC hpnil (J n.len) (hJ n.len) (hIJ n.len)
      (E n.len) (hE n.len)
  let Dm :=
    crystallineDn p I γ π hπ m.len hIC hpnil (J m.len) (hJ m.len) (hIJ m.len)
      (E m.len) (hE m.len)
  let fn :=
    crystallineDnBaseMap p I γ π hπ n.len hIC hpnil (J n.len) (hJ n.len) (hIJ n.len)
      (E n.len) (hE n.len)
  let fm :=
    crystallineDnBaseMap p I γ π hπ m.len hIC hpnil (J m.len) (hJ m.len) (hIJ m.len)
      (E m.len) (hE m.len)
  let φ := crystallineDnHom p I γ π hπ hIC hpnil J hJ hIJ E hE σ
  -- Local instance justification (instance diamond): f.toAlgebra pins Algebra A D(*) to the source base map.
  letI : Algebra A Dn := fn.toAlgebra
  -- Local instance justification (instance diamond): f.toAlgebra pins Algebra A D(*) to the source base map.
  letI : Algebra A Dm := fm.toAlgebra
  -- Local instance justification (defeq pin): pin Algebra D(n) D(m) to the simplex ring map.
  letI : Algebra Dn Dm := φ.toAlgebra
  -- Local instance justification (defeq pin): view Ω_{D(m),γ̄} as a D(n)-module by restriction of scalars.
  letI : Module Dn (dividedPowerDifferential fm (γbar m.len)) := Module.compHom _ φ
  -- Local instance justification (defeq pin): scalar tower from the simplex ring map over A.
  letI : IsScalarTower A Dn Dm :=
    IsScalarTower.of_algebraMap_eq'
      (crystallineDnHom_comp_base p I γ π hπ hIC hpnil J hJ hIJ E hE σ).symm
  { toFun := fun q ↦
      (dividedPowerRelations fm (γbar m.len)).mkQ
        (KaehlerDifferential.map A A Dn Dm (Quotient.out q))
    map_add' := sorry
    map_smul' := sorry }

/-- The uncompleted comparison is the lift of the universal derivation along the ring map. -/
theorem crystallineOmegaUncompletedHom_apply {n m : SimplexCategory} (σ : n ⟶ m)
    (x :
      let Dn :=
        crystallineDn p I γ π hπ n.len hIC hpnil (J n.len) (hJ n.len) (hIJ n.len)
          (E n.len) (hE n.len)
      let fn :=
        crystallineDnBaseMap p I γ π hπ n.len hIC hpnil (J n.len) (hJ n.len) (hIJ n.len)
          (E n.len) (hE n.len)
      -- Local instance justification (instance diamond): f.toAlgebra pins Algebra A D(*) to the source base map.
      letI : Algebra A Dn := fn.toAlgebra
      dividedPowerDifferential fn (γbar n.len)) :
    crystallineOmegaUncompletedHom p I γ π hπ hIC hpnil J hJ hIJ E hE γbar σ x =
      crystallineOmegaUncompletedHom p I γ π hπ hIC hpnil J hJ hIJ E hE γbar σ x :=
  rfl

/-- Linear comparison of completed divided-power differentials after restriction of scalars. -/
def crystallineOmegaHom {n m : SimplexCategory} (σ : n ⟶ m) :
    crystallineOmegaModuleCat p I γ π hπ hIC hpnil J hJ hIJ E hE γbar n.len ⟶
      (ModuleCat.restrictScalars
          (crystallineDnHom p I γ π hπ hIC hpnil J hJ hIJ E hE σ)).obj
        (crystallineOmegaModuleCat p I γ π hπ hIC hpnil J hJ hIJ E hE γbar m.len) :=
  let Dn :=
    crystallineDn p I γ π hπ n.len hIC hpnil (J n.len) (hJ n.len) (hIJ n.len)
      (E n.len) (hE n.len)
  let Dm :=
    crystallineDn p I γ π hπ m.len hIC hpnil (J m.len) (hJ m.len) (hIJ m.len)
      (E m.len) (hE m.len)
  let fn :=
    crystallineDnBaseMap p I γ π hπ n.len hIC hpnil (J n.len) (hJ n.len) (hIJ n.len)
      (E n.len) (hE n.len)
  let fm :=
    crystallineDnBaseMap p I γ π hπ m.len hIC hpnil (J m.len) (hJ m.len) (hIJ m.len)
      (E m.len) (hE m.len)
  let φ := crystallineDnHom p I γ π hπ hIC hpnil J hJ hIJ E hE σ
  let Ωn := dividedPowerDifferential fn (γbar n.len)
  let Ωm := dividedPowerDifferential fm (γbar m.len)
  -- Local instance justification (instance diamond): f.toAlgebra pins Algebra A D(*) to the source base map.
  letI : Algebra A Dn := fn.toAlgebra
  -- Local instance justification (instance diamond): f.toAlgebra pins Algebra A D(*) to the source base map.
  letI : Algebra A Dm := fm.toAlgebra
  -- Local instance justification (defeq pin): pin Algebra D(n) D(m) to the simplex ring map.
  letI : Algebra Dn Dm := φ.toAlgebra
  -- Local instance justification (defeq pin): view uncompleted Ω_{D(m)} as a D(n)-module.
  letI : Module Dn Ωm := Module.compHom _ φ
  -- Local instance justification (defeq pin): view completed Ω_{D(m)} as a D(n)-module.
  letI : Module Dn (AdicCompletion (Ideal.span {(p : Dm)}) Ωm) := Module.compHom _ φ
  ModuleCat.ofHom
    (Y :=
      (ModuleCat.restrictScalars φ).obj
        (crystallineOmegaModuleCat p I γ π hπ hIC hpnil J hJ hIJ E hE γbar m.len))
    { toFun := fun ω ↦
        ⟨fun k ↦
          (AdicCompletion.of (Ideal.span {(p : Dm)}) Ωm
              (crystallineOmegaUncompletedHom p I γ π hπ hIC hpnil J hJ hIJ E hE γbar σ
                (Quotient.out (ω.val k)))).val k,
          sorry⟩
      map_add' := sorry
      map_smul' := sorry }

/-- The `D(*)`-cosimplicial module with stages `Ω_{D(n)}`. -/
def crystallineOmegaDStar :
    PresheafOfModules.{u}
      (moduleRingPresheaf (crystallineDStar p I γ π hπ hIC hpnil J hJ hIJ E hE)) where
  obj X :=
    crystallineOmegaModuleCat p I γ π hπ hIC hpnil J hJ hIJ E hE γbar (unop (unop X)).len
  map {X Y} f :=
    crystallineOmegaHom p I γ π hπ hIC hpnil J hJ hIJ E hE γbar f.unop.unop
  map_id := sorry
  map_comp := sorry

/-- The degree-`n` object of `Ω_{D(*)}` is the completed relative differential module `Ω_{D(n)}`. -/
theorem crystallineOmegaDStar_obj (n : ℕ) :
    (crystallineOmegaDStar p I γ π hπ hIC hpnil J hJ hIJ E hE γbar).obj
        (op (op (SimplexCategory.mk n))) =
      crystallineOmegaModuleCat p I γ π hπ hIC hpnil J hJ hIJ E hE γbar n :=
  rfl

/-- Structure maps of `Ω_{D(*)}` are the restricted-scalar comparisons. -/
theorem crystallineOmegaDStar_map {X Y : (SimplexCategoryᵒᵖ)ᵒᵖ} (f : X ⟶ Y) :
    (crystallineOmegaDStar p I γ π hπ hIC hpnil J hJ hIJ E hE γbar).map f =
      crystallineOmegaHom p I γ π hπ hIC hpnil J hJ hIJ E hE γbar f.unop.unop :=
  rfl

/-- The bundled module object is `ModuleCat.of` on `Ω_{D(n)}`. -/
theorem crystallineOmegaModuleCat_eq (n : ℕ) :
    crystallineOmegaModuleCat p I γ π hπ hIC hpnil J hJ hIJ E hE γbar n =
      ModuleCat.of
        (crystallineDn p I γ π hπ n hIC hpnil (J n) (hJ n) (hIJ n) (E n) (hE n))
        (crystallineOmegaDn
          (crystallineDnBaseMap p I γ π hπ n hIC hpnil (J n) (hJ n) (hIJ n) (E n) (hE n))
          p (γbar n)) :=
  rfl

end CrystallineDStar

