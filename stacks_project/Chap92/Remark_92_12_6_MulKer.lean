module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Submodule
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The kernel model of `Tor_2^R(R/I, R/I)`

This leaf owns `Ker(I ⊗[R] I → I²)` as an explicit `R`-submodule of `I ⊗[R] I`, the induced
`(R ⧸ I)`-module structure, and the exterior-square comparison `⋀[R ⧸ I]^2 (I/I²) → mulKer I`.
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

universe u

namespace Algebra.CotangentComplex

variable {R : Type u} [CommRing R]

/-- The kernel of multiplication `I ⊗[R] I → I²`, as an `R`-submodule of `I ⊗[R] I`. -/
abbrev mulKer (I : Ideal R) : Submodule R (I ⊗[R] I) :=
  LinearMap.ker (Submodule.mulMap I I)

/-- `I ⊗[R] I` is an abelian group, so `mulKer I` is as well. -/
noncomputable instance instAddCommGroupTensor (I : Ideal R) : AddCommGroup (I ⊗[R] I) :=
  TensorProduct.addCommGroup

/-- Additive group structure on `mulKer I`. -/
noncomputable instance instAddCommGroupMulKer (I : Ideal R) : AddCommGroup (mulKer I) :=
  Submodule.addCommGroup (mulKer I)

/-- Membership in `mulKer I` is vanishing of `Submodule.mulMap I I`. -/
theorem mulKer_mem_iff {I : Ideal R} {x : I ⊗[R] I} :
    x ∈ mulKer I ↔ Submodule.mulMap I I x = 0 :=
  sorry

/-- The ideal `I` annihilates `mulKer I`, so `mulKer I` is an `(R ⧸ I)`-module. -/
theorem mulKer_isTorsionBySet (I : Ideal R) :
    Module.IsTorsionBySet R (mulKer I) I :=
  sorry

/-- The canonical `(R ⧸ I)`-module structure on `mulKer I`. -/
noncomputable instance instModuleMulKerQuotient (I : Ideal R) :
    Module (R ⧸ I) (mulKer I) :=
  @Function.Surjective.moduleLeft R (R ⧸ I) (mulKer I) _ AddCommGroup.toAddCommMonoid _
    (Ideal.Quotient.semiring I) (mulKer_isTorsionBySet I).hasSMul (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective sorry

/-- Transport of the quotient module structure along a surjective ring map `f : R → S`. -/
@[reducible]
noncomputable def moduleAlgebra {S : Type u} [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) : Module S (mulKer (RingHom.ker f)) :=
  Module.compHom (mulKer (RingHom.ker f))
    (f.quotientKerEquivOfSurjective hf).symm.toRingHom

/-- The object of `ModuleCat S` with carrier `mulKer (ker f)`. -/
noncomputable def mulKerModuleCat {S : Type u} [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) : ModuleCat.{u} S :=
  @ModuleCat.of S _ (mulKer (RingHom.ker f)) _ (moduleAlgebra f hf)

/-- Unfolding `mulKerModuleCat` recovers `ModuleCat.of` with `moduleAlgebra`. -/
theorem mulKerModuleCat_eq {S : Type u} [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) :
    mulKerModuleCat f hf =
      @ModuleCat.of S _ (mulKer (RingHom.ker f)) _ (moduleAlgebra f hf) :=
  sorry

/-- The alternating tensor `a ⊗ₜ b - b ⊗ₜ a` lies in `mulKer I`. -/
theorem tmul_sub_mem_mulKer {I : Ideal R} (a b : I) :
    a ⊗ₜ b - b ⊗ₜ a ∈ mulKer I :=
  sorry

/-- The element `a ⊗ₜ b - b ⊗ₜ a` of `mulKer I`. -/
noncomputable def alternTmul {I : Ideal R} (a b : I) : mulKer I :=
  ⟨a ⊗ₜ b - b ⊗ₜ a, tmul_sub_mem_mulKer a b⟩

/-- Unfolding `alternTmul` recovers the alternating elementary tensor. -/
theorem alternTmul_coe {I : Ideal R} (a b : I) :
    (alternTmul a b : I ⊗[R] I) = a ⊗ₜ b - b ⊗ₜ a :=
  sorry

/-- Pairing of two conormal classes with values in `mulKer I`. -/
noncomputable def conormalPair (I : Ideal R) (x y : I.Cotangent) : mulKer I :=
  Quotient.liftOn₂ x y (fun a b => alternTmul a b) sorry

/-- The alternating map on two conormal classes with values in `mulKer I`. -/
noncomputable def conormalExteriorSquareAlternating (I : Ideal R) :
    I.Cotangent [⋀^Fin 2]→ₗ[R ⧸ I] mulKer I where
  toFun v := conormalPair I (v 0) (v 1)
  map_update_add' := sorry
  map_update_smul' := sorry
  map_eq_zero_of_eq' := sorry

/-- The comparison `⋀[R ⧸ I]^2 (I/I²) → mulKer I` sending `ā ∧ b̄` to `a ⊗ₜ b - b ⊗ₜ a`. -/
noncomputable def conormalExteriorSquareToMulKer (I : Ideal R) :
    ⋀[R ⧸ I]^2 I.Cotangent →+ mulKer I :=
  (exteriorPower.alternatingMapLinearEquiv (conormalExteriorSquareAlternating I)).toAddMonoidHom

/-- On decomposable wedges, `conormalExteriorSquareToMulKer` recovers `alternTmul`. -/
theorem conormalExteriorSquareToMulKer_apply (I : Ideal R) (a b : I) :
    conormalExteriorSquareToMulKer I
        (exteriorPower.ιMulti (R ⧸ I) 2 fun i =>
          if i = 0 then I.toCotangent a else I.toCotangent b) =
      alternTmul a b :=
  sorry

end Algebra.CotangentComplex
