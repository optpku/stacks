/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Extension.FirstOrder
public import ReasLib.RingTheory.Kaehler.BaseChange
public import Mathlib.RingTheory.Unramified.Basic
import Mathlib.Tactic.CrossRefAttribute
import ReasLib.LinearAlgebra.TensorProduct.Surjective
import Mathlib.Algebra.TrivSqZeroExt.Ideal

/-!
# Universal First-Order Thickenings of Unramified Algebras

This file records the formal-unramifiedness and Kähler comparison properties
of a universal first-order thickening.  The comparison map itself is the
presentation-independent `KaehlerDifferential.tensorMapBaseChange`.

@stack 04EF
-/

@[expose] public section

noncomputable section

open Algebra
open scoped TensorProduct

universe u v w x y

namespace Algebra.Extension.FirstOrder.IsUniversal

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
variable {P : Extension.{x} A B}

private noncomputable def twisted
    {M : Type y} [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M]
    [IsCentralScalar B M] [Module A M] [Module R M]
    [IsScalarTower A B M] [IsScalarTower R B M]
    (dA : Derivation R A M) : A →ₐ[R] TrivSqZeroExt B M where
  toFun a := ⟨algebraMap A B a, dA a⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp [dA.leibniz]
  commutes' r := by
    ext
    · change algebraMap A B (algebraMap R A r) = algebraMap R B r
      exact (IsScalarTower.algebraMap_apply R A B r).symm
    · change dA (algebraMap R A r) = 0
      exact dA.map_algebraMap r

/-- The universal lifting property, applied to a trivial square-zero
extension, uniquely extends derivations from the base to the thickening. -/
@[stacks 04EF "unique extension of derivations to the thickening"]
theorem existsUniqueDerivation
    {M : Type y} [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M]
    [IsCentralScalar B M] [Module A M] [Module R M]
    [IsScalarTower A B M] [IsScalarTower R B M]
    {P : Extension.{x} A B}
    [Module P.Ring M] [IsScalarTower A P.Ring M] [IsScalarTower P.Ring B M]
    (hP : IsUniversal.{max x (max v (max w y))} P)
    (dA : Derivation R A M) :
    ∃! dP : Derivation R P.Ring M, dP.compAlgebraMap A = dA := by
  let C := TrivSqZeroExt B M
  let α : A →ₐ[R] C := twisted (A := A) (B := B) dA
  -- Proof-local instance justification (explicit-map choice): this `A`-algebra structure varies
  -- with `dA`, so it cannot be a canonical global instance on `TrivSqZeroExt B M`.
  letI : Algebra A C := α.toAlgebra
  let q : C →ₐ[A] B :=
    { (TrivSqZeroExt.fstHom B B M).toRingHom with
      commutes' := fun a => by
        change (α a).fst = algebraMap A B a
        rfl }
  have hq : Function.Surjective q := by
    intro b
    exact ⟨TrivSqZeroExt.inl b, rfl⟩
  let I : Ideal C := TrivSqZeroExt.kerIdeal B M
  let e : (C ⧸ I) ≃ₐ[A] B :=
    Ideal.quotientKerAlgEquivOfSurjective (f := q) hq
  let f : B →ₐ[A] C ⧸ I := e.symm.toAlgHom
  obtain ⟨g, hg, huniq⟩ :=
    @IsUniversal.existsUniqueLift.{v, w, x, max w y, max x v}
      A B _ _ _ P hP C _ _ I (TrivSqZeroExt.kerIdeal_sq B M) f
  have hg_fst (p : P.Ring) : (g p).fst = algebraMap P.Ring B p := by
    have hp := DFunLike.congr_fun hg p
    change Ideal.Quotient.mk I (g p) = e.symm (algebraMap P.Ring B p) at hp
    calc
      (g p).fst = q (g p) := rfl
      _ = e (Ideal.Quotient.mk I (g p)) := by
        exact (Ideal.quotientKerAlgEquivOfSurjective_mk (f := q) hq (g p)).symm
      _ = e (e.symm (algebraMap P.Ring B p)) := by rw [hp]
      _ = algebraMap P.Ring B p := e.apply_symm_apply _
  let dPLinear : P.Ring →ₗ[R] M :=
    { toFun := fun p => (g p).snd
      map_add' := fun p q' => by rw [map_add, TrivSqZeroExt.snd_add]
      map_smul' := fun r p => by
        rw [Algebra.smul_def, map_mul, TrivSqZeroExt.snd_mul, hg_fst]
        have hsnd : (g (algebraMap R P.Ring r)).snd = 0 := by
          rw [show algebraMap R P.Ring r =
              algebraMap A P.Ring (algebraMap R A r) by
            exact IsScalarTower.algebraMap_apply R A P.Ring r]
          rw [g.commutes]
          change dA (algebraMap R A r) = 0
          exact dA.map_algebraMap r
        rw [hsnd, smul_zero, add_zero]
        rw [← IsScalarTower.algebraMap_apply R P.Ring B r]
        exact IsScalarTower.algebraMap_smul (R := R) (A := B) r (g p).snd }
  let dP : Derivation R P.Ring M := Derivation.mk' dPLinear fun p q' => by
    change (g (p * q')).snd = p • (g q').snd + q' • (g p).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, hg_fst, hg_fst, op_smul_eq_smul,
      IsScalarTower.algebraMap_smul (R := P.Ring) (A := B),
      IsScalarTower.algebraMap_smul (R := P.Ring) (A := B)]
  have hdP : dP.compAlgebraMap A = dA := by
    apply Derivation.ext
    intro a
    change (g (algebraMap A P.Ring a)).snd = dA a
    rw [g.commutes]
    rfl
  refine ⟨dP, hdP, ?_⟩
  intro d hd
  let gd : P.Ring →ₐ[A] C :=
    { toFun := fun p => ⟨algebraMap P.Ring B p, d p⟩
      map_zero' := by ext <;> simp
      map_one' := by ext <;> simp
      map_add' := fun p q' => by
        ext
        · change algebraMap P.Ring B (p + q') =
            algebraMap P.Ring B p + algebraMap P.Ring B q'
          exact map_add (algebraMap P.Ring B) p q'
        · change d (p + q') = d p + d q'
          exact d.map_add p q'
      map_mul' := fun p q' => by
        ext
        · change algebraMap P.Ring B (p * q') =
            algebraMap P.Ring B p * algebraMap P.Ring B q'
          exact (algebraMap P.Ring B).map_mul p q'
        · change d (p * q') =
            algebraMap P.Ring B p • d q' +
              MulOpposite.op (algebraMap P.Ring B q') • d p
          rw [d.leibniz, op_smul_eq_smul,
            IsScalarTower.algebraMap_smul (R := P.Ring) (A := B),
            IsScalarTower.algebraMap_smul (R := P.Ring) (A := B)]
      commutes' := fun a => by
        ext
        · change algebraMap P.Ring B (algebraMap A P.Ring a) = algebraMap A B a
          exact (IsScalarTower.algebraMap_apply A P.Ring B a).symm
        · change d (algebraMap A P.Ring a) = dA a
          exact Derivation.congr_fun hd a }
  have hgd :
      (Ideal.Quotient.mkₐ A I).comp gd =
        f.comp (IsScalarTower.toAlgHom A P.Ring B) := by
    apply AlgHom.ext
    intro p
    apply e.injective
    change e (Ideal.Quotient.mk I (gd p)) =
      e (e.symm (algebraMap P.Ring B p))
    calc
      e (Ideal.Quotient.mk I (gd p)) = q (gd p) :=
        Ideal.quotientKerAlgEquivOfSurjective_mk (f := q) hq (gd p)
      _ = algebraMap P.Ring B p := rfl
      _ = e (e.symm (algebraMap P.Ring B p)) := (e.apply_symm_apply _).symm
  have hgd_eq : gd = g := huniq gd hgd
  apply Derivation.ext
  intro p
  have hp := congrArg TrivSqZeroExt.snd (DFunLike.congr_fun hgd_eq p)
  simpa [dP, dPLinear, gd] using hp

/-- A universal first-order thickening preserves relative Kähler
differentials after extension to its target. -/
private theorem tensorMapBaseChange_bijective_aux
    {P : Extension.{x} A B}
    (hP : IsUniversal.{max x (max v w)} P) :
    Function.Bijective
      (KaehlerDifferential.tensorMapBaseChange R A P.Ring B) := by
  let MA := B ⊗[A] Ω[A⁄R]
  let MP := B ⊗[P.Ring] Ω[P.Ring⁄R]
  let iA : Ω[A⁄R] →ₗ[A] MA := (TensorProduct.mk A B Ω[A⁄R]) 1
  let dA : Derivation R A MA := iA.compDer (KaehlerDifferential.D R A)
  obtain ⟨dP, hdP, -⟩ := existsUniqueDerivation (M := MA) hP dA
  let iP : Ω[P.Ring⁄R] →ₗ[P.Ring] MP :=
    (TensorProduct.mk P.Ring B Ω[P.Ring⁄R]) 1
  let φ : MA →ₗ[B] MP := KaehlerDifferential.tensorMapBaseChange R A P.Ring B
  let ψ : MP →ₗ[B] MA :=
    (TensorProduct.isBaseChange P.Ring Ω[P.Ring⁄R] B).lift
      dP.liftKaehlerDifferential
  have hΩA : ((ψ.comp φ).restrictScalars A).comp iA = iA := by
    apply Derivation.liftKaehlerDifferential_unique
    apply Derivation.ext
    intro a
    change ψ (φ (1 ⊗ₜ[A] KaehlerDifferential.D R A a)) =
      1 ⊗ₜ[A] KaehlerDifferential.D R A a
    rw [show φ (1 ⊗ₜ[A] KaehlerDifferential.D R A a) =
        1 ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring (algebraMap A P.Ring a) by
      change KaehlerDifferential.tensorMapBaseChange R A P.Ring B
          (1 ⊗ₜ[A] KaehlerDifferential.D R A a) = _
      rw [KaehlerDifferential.tensorMapBaseChange_tmul,
        KaehlerDifferential.map_D]]
    rw [show ψ
        (1 ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring (algebraMap A P.Ring a)) =
        dP (algebraMap A P.Ring a) by
      change (TensorProduct.isBaseChange P.Ring Ω[P.Ring⁄R] B).lift
          dP.liftKaehlerDifferential
          ((TensorProduct.mk P.Ring B Ω[P.Ring⁄R]) 1
            (KaehlerDifferential.D R P.Ring (algebraMap A P.Ring a))) = _
      rw [(TensorProduct.isBaseChange P.Ring Ω[P.Ring⁄R] B).lift_eq,
        Derivation.liftKaehlerDifferential_comp_D]]
    have ha := Derivation.congr_fun hdP a
    change dP (algebraMap A P.Ring a) = dA a at ha
    change dP (algebraMap A P.Ring a) =
      (TensorProduct.mk A B Ω[A⁄R]) 1 (KaehlerDifferential.D R A a) at ha
    change dP (algebraMap A P.Ring a) =
      (TensorProduct.mk A B Ω[A⁄R]) 1 (KaehlerDifferential.D R A a)
    exact ha
  have hleft : ψ.comp φ = LinearMap.id := by
    apply (TensorProduct.isBaseChange A Ω[A⁄R] B).algHom_ext
    intro z
    change ψ (φ (1 ⊗ₜ[A] z)) = 1 ⊗ₜ[A] z
    exact LinearMap.congr_fun hΩA z
  let dA' : Derivation R A MP := (φ.restrictScalars A).compDer dA
  let dP' : Derivation R P.Ring MP := (φ.restrictScalars P.Ring).compDer dP
  let dPcanon : Derivation R P.Ring MP :=
    iP.compDer (KaehlerDifferential.D R P.Ring)
  obtain ⟨d0, -, huniq⟩ := existsUniqueDerivation (M := MP) hP dA'
  have hdP' : dP'.compAlgebraMap A = dA' := by
    apply Derivation.ext
    intro a
    change φ (dP (algebraMap A P.Ring a)) = φ (dA a)
    have ha := Derivation.congr_fun hdP a
    change dP (algebraMap A P.Ring a) = dA a at ha
    rw [ha]
  have hdPcanon : dPcanon.compAlgebraMap A = dA' := by
    apply Derivation.ext
    intro a
    change 1 ⊗ₜ[P.Ring]
        KaehlerDifferential.D R P.Ring (algebraMap A P.Ring a) =
      φ (1 ⊗ₜ[A] KaehlerDifferential.D R A a)
    change _ = KaehlerDifferential.tensorMapBaseChange R A P.Ring B
      (1 ⊗ₜ[A] KaehlerDifferential.D R A a)
    rw [KaehlerDifferential.tensorMapBaseChange_tmul,
      KaehlerDifferential.map_D]
  have hder : dP' = dPcanon :=
    (huniq dP' hdP').trans (huniq dPcanon hdPcanon).symm
  have hΩP : ((φ.comp ψ).restrictScalars P.Ring).comp iP = iP := by
    apply Derivation.liftKaehlerDifferential_unique
    apply Derivation.ext
    intro p
    change φ (ψ (1 ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring p)) =
      1 ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring p
    rw [show ψ (1 ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring p) = dP p by
      change (TensorProduct.isBaseChange P.Ring Ω[P.Ring⁄R] B).lift
          dP.liftKaehlerDifferential
          ((TensorProduct.mk P.Ring B Ω[P.Ring⁄R]) 1
            (KaehlerDifferential.D R P.Ring p)) = _
      rw [(TensorProduct.isBaseChange P.Ring Ω[P.Ring⁄R] B).lift_eq,
        Derivation.liftKaehlerDifferential_comp_D]]
    exact Derivation.congr_fun hder p
  have hright : φ.comp ψ = LinearMap.id := by
    apply (TensorProduct.isBaseChange P.Ring Ω[P.Ring⁄R] B).algHom_ext
    intro z
    change φ (ψ (1 ⊗ₜ[P.Ring] z)) = 1 ⊗ₜ[P.Ring] z
    exact LinearMap.congr_fun hΩP z
  have hli : Function.LeftInverse ψ φ := fun z => by
    simpa using LinearMap.congr_fun hleft z
  have hri : Function.RightInverse ψ φ := fun z => by
    simpa using LinearMap.congr_fun hright z
  exact ⟨hli.injective, hri.surjective⟩

/-- The source ring of a universal first-order thickening is formally
unramified over the base. -/
@[stacks 04EF "(1), formal unramifiedness of the thickening"]
theorem formallyUnramified
    (hP : IsUniversal.{max x (max v w)} P) :
    Algebra.FormallyUnramified A P.Ring := by
  let M := Ω[P.Ring⁄A]
  let iP : M →ₗ[P.Ring] B ⊗[P.Ring] M :=
    (TensorProduct.mk P.Ring B M) 1
  have hbij : Function.Bijective
      (KaehlerDifferential.tensorMapBaseChange A A P.Ring B) :=
    tensorMapBaseChange_bijective_aux (R := A) hP
  have htarget : Subsingleton (B ⊗[P.Ring] M) := hbij.2.subsingleton
  have hker : LinearMap.ker iP = ⊤ := by
    rw [LinearMap.ker_eq_top]
    ext z
    exact @Subsingleton.elim _ htarget _ _
  have hJM : P.ker • (⊤ : Submodule P.Ring M) = ⊤ := by
    rw [← LinearMap.ker_tensorProductMk_of_surjective P.algebraMap_surjective]
    exact hker
  constructor
  apply subsingleton_iff_forall_eq 0 |>.mpr
  intro m
  have hm1 : m ∈ P.ker • (⊤ : Submodule P.Ring M) := by
    rw [hJM]
    exact Submodule.mem_top
  have hm2 : m ∈ P.ker • (P.ker • (⊤ : Submodule P.Ring M)) := by
    rw [hJM]
    exact hm1
  have hsq : P.ker * P.ker = ⊥ := by
    simpa [pow_two] using hP.squareZero
  have : m ∈ (⊥ : Submodule P.Ring M) := by
    rw [← Submodule.mul_smul, hsq] at hm2
    simpa only [Submodule.bot_smul] using hm2
  simpa using this

/-- For a universal first-order thickening, the tensor-extended Kähler
base-change map is bijective. -/
@[stacks 04EF "(2), bijective Kaehler comparison"]
theorem tensorMapBaseChange_bijective
    (hP : IsUniversal.{max x (max v w)} P) :
    Function.Bijective
      (KaehlerDifferential.tensorMapBaseChange R A P.Ring B) :=
  tensorMapBaseChange_bijective_aux hP

end Algebra.Extension.FirstOrder.IsUniversal
