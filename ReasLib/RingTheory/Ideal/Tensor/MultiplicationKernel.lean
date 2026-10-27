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
    Module.IsTorsionBySet R (mulKer I) I := sorry

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
    a ⊗ₜ b - b ⊗ₜ a ∈ mulKer I := sorry

/-- The alternating elementary tensor in the multiplication kernel. -/
def alternTmul {I : Ideal R} (a b : I) : mulKer I :=
  ⟨a ⊗ₜ b - b ⊗ₜ a, tmul_sub_mem_mulKer a b⟩

/-- The underlying tensor of the alternating elementary tensor is its defining difference. -/
theorem alternTmul_coe {I : Ideal R} (a b : I) :
    (alternTmul a b : I ⊗[R] I) = a ⊗ₜ b - b ⊗ₜ a := rfl

/-- Alternating tensors depend only on the conormal classes of their arguments. -/
theorem conormalPair_wellDefined (I : Ideal R) (a b c d : I)
    (hac : (a : R) - c ∈ I ^ 2) (hbd : (b : R) - d ∈ I ^ 2) :
    alternTmul a b = alternTmul c d := sorry

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
        conormalPair I (Function.update v i y 0) (Function.update v i y 1) := sorry

/-- The conormal tensor pairing is linear over the quotient ring in each coordinate. -/
theorem conormalExteriorSquareAlternating_map_update_smul (I : Ideal R)
    [DecidableEq (Fin 2)] (v : Fin 2 → I.Cotangent) (i : Fin 2) (r : R ⧸ I)
    (x : I.Cotangent) :
    (conormalPair I (Function.update v i (r • x) 0) (Function.update v i (r • x) 1) :
      mulKerQuotientModuleCat I) =
      HSMul.hSMul (α := R ⧸ I) (β := mulKerQuotientModuleCat I)
        (γ := mulKerQuotientModuleCat I) r
        (conormalPair I (Function.update v i x 0) (Function.update v i x 1)) := sorry

/-- The conormal tensor pairing vanishes when two distinct coordinates agree. -/
theorem conormalExteriorSquareAlternating_map_eq_zero_of_eq (I : Ideal R)
    (v : Fin 2 → I.Cotangent) (i j : Fin 2) (h : v i = v j) (hij : i ≠ j) :
    conormalPair I (v 0) (v 1) = 0 := sorry

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
      alternTmul a b := sorry

variable {S : Type v} [CommRing S]

/-- Tensoring a compatible ring map preserves the kernel of ideal multiplication. -/
theorem mulKerMap_mem (f : R →+* S) {I : Ideal R} {J : Ideal S}
    (h : I ≤ Ideal.comap f J) (x : I ⊗[R] I) (hx : x ∈ mulKer I) :
    TensorProduct.map (f.toSemilinearMap.restrict h) (f.toSemilinearMap.restrict h) x ∈
      mulKer J := sorry

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
      alternTmul ⟨f a, h a.2⟩ ⟨f b, h b.2⟩ := sorry

end Ideal
