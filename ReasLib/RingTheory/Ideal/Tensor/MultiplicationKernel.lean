/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.LinearAlgebra.TensorProduct.Submodule
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.FinCases

/-!
# Multiplication kernels of ideal tensor squares

The kernel of ideal multiplication has quotient-ring scalars and receives an
alternating comparison from the exterior square of the conormal module.
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

universe u v

namespace Ideal

variable {R : Type u} [CommRing R]

/-- The kernel of multiplication from the tensor square of an ideal to its ring. -/
abbrev mulKer (I : Ideal R) : Submodule R (I ⊗[R] I) :=
  LinearMap.ker (Submodule.mulMap I I)

/-- Membership in the multiplication kernel means that the product is zero. -/
theorem mulKer_mem_iff {I : Ideal R} {x : I ⊗[R] I} :
    x ∈ mulKer I ↔ Submodule.mulMap I I x = 0 := Iff.rfl

/-- An ideal annihilates the kernel of multiplication on its tensor square. -/
theorem mulKer_isTorsionBySet (I : Ideal R) :
    Module.IsTorsionBySet R (mulKer I) I := by
  intro x a
  let m : I ⊗[R] I →ₗ[R] I :=
    TensorProduct.lift ((LinearMap.lsmul R I).comp I.subtype)
  have hm (y : I ⊗[R] I) : (m y : R) = Submodule.mulMap I I y := by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul b c => rfl
    | add y z hy hz => simp [hy, hz]
  have hx : m x.1 = 0 := Subtype.ext ((hm x.1).trans x.2)
  have ha (y : I ⊗[R] I) : (a : R) • y = a ⊗ₜ[R] m y := by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul b c =>
      change (a : R) • (b ⊗ₜ[R] c) = a ⊗ₜ[R] ((b : R) • c)
      rw [TensorProduct.smul_tmul', ← TensorProduct.smul_tmul]
      congr 1
      exact Subtype.ext (mul_comm _ _)
    | add y z hy hz => simp [smul_add, hy, hz, TensorProduct.tmul_add]
  apply Subtype.ext
  change (a : R) • x.1 = 0
  rw [ha, hx, TensorProduct.tmul_zero]

/-- The multiplication kernel as a module over the quotient by the ideal. -/
def mulKerQuotientModuleCat (I : Ideal R) : ModuleCat.{u} (R ⧸ I) :=
  @ModuleCat.of (R ⧸ I) _ (mulKer I) _ (mulKer_isTorsionBySet I).module

/-- The multiplication kernel of a surjection, with scalars transported to its target. -/
@[reducible]
def mulKerModule {S : Type v} [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) : Module S (mulKer (RingHom.ker f)) :=
  @Module.compHom (R ⧸ RingHom.ker f) S (mulKer (RingHom.ker f)) _ _
    (mulKerQuotientModuleCat (RingHom.ker f)).isModule _
    (f.quotientKerEquivOfSurjective hf).symm.toRingHom

/-- The multiplication kernel of a surjection as a module over its target. -/
def mulKerModuleCat {S : Type v} [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) : ModuleCat.{u} S :=
  @ModuleCat.of S _ (mulKer (RingHom.ker f)) _ (mulKerModule f hf)

/-- The difference of the two ordered elementary tensors has zero product. -/
theorem tmul_sub_mem_mulKer {I : Ideal R} (a b : I) :
    a ⊗ₜ b - b ⊗ₜ a ∈ mulKer I := by
  simp [mul_comm]

/-- The alternating elementary tensor in the multiplication kernel. -/
def alternTmul {I : Ideal R} (a b : I) : mulKer I :=
  ⟨a ⊗ₜ b - b ⊗ₜ a, tmul_sub_mem_mulKer a b⟩

/-- The underlying tensor of the alternating elementary tensor is its defining difference. -/
theorem alternTmul_coe {I : Ideal R} (a b : I) :
    (alternTmul a b : I ⊗[R] I) = a ⊗ₜ b - b ⊗ₜ a := rfl

/-- Alternating tensors depend only on the conormal classes of their arguments. -/
theorem conormalPair_wellDefined (I : Ideal R) (a b c d : I)
    (hac : (a : R) - c ∈ I ^ 2) (hbd : (b : R) - d ∈ I ^ 2) :
    alternTmul a b = alternTmul c d := by
  have hleft (x y z : I) (hxy : (x : R) - y ∈ I ^ 2) :
      x ⊗ₜ[R] z - z ⊗ₜ[R] x = y ⊗ₜ[R] z - z ⊗ₜ[R] y := by
    let g : I →ₗ[R] I ⊗[R] I :=
      (TensorProduct.mk R I I).flip z - TensorProduct.mk R I I z
    have hzero (t : I) (ht : (t : R) ∈ I ^ 2) : g t = 0 := by
      have ht' : t ∈ I • (⊤ : Submodule R I) :=
        (Submodule.Quotient.mk_eq_zero _).mp ((I.toCotangent_eq_zero t).mpr ht)
      refine Submodule.smul_induction_on ht' ?_ ?_
      · intro r hr s _
        rw [map_smul]
        exact congrArg Subtype.val
          (mulKer_isTorsionBySet I (x := alternTmul s z) (a := ⟨r, hr⟩))
      · intro s t hs ht
        simp [map_add, hs, ht]
    have heq := hzero (x - y) hxy
    rw [map_sub, sub_eq_zero] at heq
    exact heq
  apply Subtype.ext
  change a ⊗ₜ[R] b - b ⊗ₜ[R] a = c ⊗ₜ[R] d - d ⊗ₜ[R] c
  calc
    _ = c ⊗ₜ[R] b - b ⊗ₜ[R] c := hleft a c b hac
    _ = c ⊗ₜ[R] d - d ⊗ₜ[R] c := by
      simpa only [neg_sub] using congrArg Neg.neg (hleft b d c hbd)

/-- The alternating tensor pairing of conormal classes. -/
def conormalPair (I : Ideal R) (x y : I.Cotangent) : mulKer I :=
  Quotient.liftOn₂ x y (fun a b => alternTmul a b)
    (fun a b c d hac hbd => conormalPair_wellDefined I a b c d
      (I.toCotangent_eq.mp (Quotient.sound hac))
      (I.toCotangent_eq.mp (Quotient.sound hbd)))

/-- The conormal tensor pairing is additive in each coordinate. -/
theorem conormalExteriorSquareAlternating_map_update_add (I : Ideal R)
    [DecidableEq (Fin 2)] (v : Fin 2 → I.Cotangent) (i : Fin 2) (x y : I.Cotangent) :
    conormalPair I (Function.update v i (x + y) 0) (Function.update v i (x + y) 1) =
      conormalPair I (Function.update v i x 0) (Function.update v i x 1) +
        conormalPair I (Function.update v i y 0) (Function.update v i y 1) := by
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
  obtain ⟨y, rfl⟩ := I.toCotangent_surjective y
  have hi : i = 0 ∨ i = 1 :=
    Fin.cases (motive := fun k : Fin 2 => k = 0 ∨ k = 1) (Or.inl rfl)
      (fun j => Or.inr (congrArg Fin.succ (Subsingleton.elim j 0))) i
  rcases hi with rfl | rfl
  · simp only [Function.update_self, Function.update_of_ne (by intro e; cases congrArg Fin.val e : (1 : Fin 2) ≠ 0)]
    obtain ⟨b, hb⟩ := I.toCotangent_surjective (v 1)
    rw [← map_add, ← hb]
    apply Subtype.ext
    change (x + y) ⊗ₜ[R] b - b ⊗ₜ[R] (x + y) =
      (x ⊗ₜ[R] b - b ⊗ₜ[R] x) + (y ⊗ₜ[R] b - b ⊗ₜ[R] y)
    rw [TensorProduct.add_tmul, TensorProduct.tmul_add, sub_add_sub_comm]
  · simp only [Function.update_self, Function.update_of_ne (by intro e; cases congrArg Fin.val e : (0 : Fin 2) ≠ 1)]
    obtain ⟨a, ha⟩ := I.toCotangent_surjective (v 0)
    rw [← map_add, ← ha]
    apply Subtype.ext
    change a ⊗ₜ[R] (x + y) - (x + y) ⊗ₜ[R] a =
      (a ⊗ₜ[R] x - x ⊗ₜ[R] a) + (a ⊗ₜ[R] y - y ⊗ₜ[R] a)
    rw [TensorProduct.add_tmul, TensorProduct.tmul_add, sub_add_sub_comm]

/-- The conormal tensor pairing is linear over the quotient ring in each coordinate. -/
theorem conormalExteriorSquareAlternating_map_update_smul (I : Ideal R)
    [DecidableEq (Fin 2)] (v : Fin 2 → I.Cotangent) (i : Fin 2) (r : R ⧸ I)
    (x : I.Cotangent) :
    (conormalPair I (Function.update v i (r • x) 0) (Function.update v i (r • x) 1) :
      mulKerQuotientModuleCat I) =
      HSMul.hSMul (α := R ⧸ I) (β := mulKerQuotientModuleCat I)
        (γ := mulKerQuotientModuleCat I) r
        (conormalPair I (Function.update v i x 0) (Function.update v i x 1)) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
  have hi : i = 0 ∨ i = 1 :=
    Fin.cases (motive := fun k : Fin 2 => k = 0 ∨ k = 1) (Or.inl rfl)
      (fun j => Or.inr (congrArg Fin.succ (Subsingleton.elim j 0))) i
  rcases hi with rfl | rfl
  · simp only [Function.update_self, Function.update_of_ne (by intro e; cases congrArg Fin.val e : (1 : Fin 2) ≠ 0)]
    obtain ⟨b, hb⟩ := I.toCotangent_surjective (v 1)
    rw [← hb]
    change alternTmul (r • x) b = r • alternTmul x b
    apply Subtype.ext
    change (r • x) ⊗ₜ[R] b - b ⊗ₜ[R] (r • x) =
      r • (x ⊗ₜ[R] b - b ⊗ₜ[R] x)
    simp [← TensorProduct.smul_tmul', smul_sub]
  · simp only [Function.update_self, Function.update_of_ne (by intro e; cases congrArg Fin.val e : (0 : Fin 2) ≠ 1)]
    obtain ⟨a, ha⟩ := I.toCotangent_surjective (v 0)
    rw [← ha]
    change alternTmul a (r • x) = r • alternTmul a x
    apply Subtype.ext
    change a ⊗ₜ[R] (r • x) - (r • x) ⊗ₜ[R] a =
      r • (a ⊗ₜ[R] x - x ⊗ₜ[R] a)
    simp [← TensorProduct.smul_tmul', smul_sub]

/-- The conormal tensor pairing vanishes when two distinct coordinates agree. -/
theorem conormalExteriorSquareAlternating_map_eq_zero_of_eq (I : Ideal R)
    (v : Fin 2 → I.Cotangent) (i j : Fin 2) (h : v i = v j) (hij : i ≠ j) :
    conormalPair I (v 0) (v 1) = 0 := by
  have h01 : v 0 = v 1 := by
    fin_cases i <;> fin_cases j <;> simp_all
  rw [h01]
  obtain ⟨a, ha⟩ := I.toCotangent_surjective (v 1)
  rw [← ha]
  apply Subtype.ext
  exact sub_self _

/-- The alternating conormal pairing with values in the quotient-ring multiplication kernel. -/
def conormalExteriorSquareAlternating (I : Ideal R) :
    I.Cotangent [⋀^Fin 2]→ₗ[R ⧸ I] mulKerQuotientModuleCat I where
  toFun v := conormalPair I (v 0) (v 1)
  map_update_add' := conormalExteriorSquareAlternating_map_update_add I
  map_update_smul' := conormalExteriorSquareAlternating_map_update_smul I
  map_eq_zero_of_eq' := conormalExteriorSquareAlternating_map_eq_zero_of_eq I

/-- The quotient-ring-linear comparison from the conormal exterior square to the tensor kernel. -/
def conormalExteriorSquareToMulKer (I : Ideal R) :
    ⋀[R ⧸ I]^2 I.Cotangent →ₗ[R ⧸ I] mulKerQuotientModuleCat I :=
  exteriorPower.alternatingMapLinearEquiv (conormalExteriorSquareAlternating I)

/-- The conormal exterior comparison sends a decomposable wedge to its alternating tensor. -/
theorem conormalExteriorSquareToMulKer_apply (I : Ideal R) (a b : I) :
    conormalExteriorSquareToMulKer I
        (exteriorPower.ιMulti (R ⧸ I) 2 fun i =>
          if i = 0 then I.toCotangent a else I.toCotangent b) =
      alternTmul a b := by
  rw [conormalExteriorSquareToMulKer,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  change conormalPair I (I.toCotangent a) (I.toCotangent b) = alternTmul a b
  rfl

variable {S : Type v} [CommRing S]

/-- Tensoring a compatible ring map preserves the kernel of ideal multiplication. -/
theorem mulKerMap_mem (f : R →+* S) {I : Ideal R} {J : Ideal S}
    (h : I ≤ Ideal.comap f J) (x : I ⊗[R] I) (hx : x ∈ mulKer I) :
    TensorProduct.map (f.toSemilinearMap.restrict h) (f.toSemilinearMap.restrict h) x ∈
      mulKer J := by
  have hm (y : I ⊗[R] I) :
      Submodule.mulMap J J
        (TensorProduct.map (f.toSemilinearMap.restrict h) (f.toSemilinearMap.restrict h) y) =
      f (Submodule.mulMap I I y) := by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => exact (map_mul f (a : R) (b : R)).symm
    | add y z hy hz => simp [hy, hz]
  change Submodule.mulMap I I x = 0 at hx
  rw [mulKer_mem_iff, hm, hx, map_zero]

/-- The additive map on multiplication kernels induced by a compatible ring homomorphism. -/
def mulKerMap (f : R →+* S) {I : Ideal R} {J : Ideal S}
    (h : I ≤ Ideal.comap f J) : mulKer I →+ mulKer J :=
  AddMonoidHom.codRestrict
    ((TensorProduct.map (f.toSemilinearMap.restrict h)
        (f.toSemilinearMap.restrict h)).toAddMonoidHom.comp
      (Submodule.subtype (mulKer I)).toAddMonoidHom)
    (mulKer J) (fun x => mulKerMap_mem f h x x.2)

/-- A ring-induced multiplication-kernel map preserves alternating elementary tensors. -/
theorem mulKerMap_alternTmul (f : R →+* S) {I : Ideal R} {J : Ideal S}
    (h : I ≤ Ideal.comap f J) (a b : I) :
    mulKerMap f h (alternTmul a b) =
      alternTmul ⟨f a, h a.2⟩ ⟨f b, h b.2⟩ := by
  apply Subtype.ext
  change TensorProduct.map (f.toSemilinearMap.restrict h) (f.toSemilinearMap.restrict h)
    (a ⊗ₜ[R] b - b ⊗ₜ[R] a) = _
  rw [map_sub, TensorProduct.map_tmul, TensorProduct.map_tmul]
  rfl

end Ideal
