module

public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.RingTheory.Derivation.Basic
public import stacks_project.Chap90.Definition_90_7_3_FormalObject
public import stacks_project.Chap90.Definition_90_12_1_TangentSpace

/-!
# Differential of a formal object

A derivation `D : Derivation Λ R k` induces a dual-number lift of the first maximal-adic
truncation of a formal object `ξ` over `R`. The differential records the isomorphism class
of the cofibered pushforward of that stage in the canonical tangent space `Functor.tangentSpace`.
-/

@[expose] public section

open CategoryTheory IsLocalRing TrivSqZeroExt
open Functor

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]

noncomputable section

namespace CompleteLocalAlgCat

/-- Residue-field identification of a complete local algebra as an `R`-algebra structure on `k`. -/
instance algebra_residue (R : CompleteLocalAlgCat Λ k) : Algebra R.carrier k :=
  (R.residueFieldIso.toAlgHom.toRingHom.comp (residue R.carrier)).toAlgebra

/-- The tower `Λ → R → k` for the residue identification of a complete local algebra. -/
instance isScalarTower_residue (R : CompleteLocalAlgCat Λ k) :
    IsScalarTower Λ R.carrier k := sorry

end CompleteLocalAlgCat

namespace CategoryTheory.Functor

/-- Predeformation categories are cofibered, so `p.op` is prefibered. -/
instance instIsPreFibered_op (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsPredeformationCategory p] : IsPreFibered p.op :=
  IsPredeformationCategory.isCofiberedInGroupoids.toIsFibered.toIsPreFibered

end CategoryTheory.Functor

namespace FormalObject

variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

/-- The dual-number algebra map `r ↦ inl (residue r) + inr (D r)` associated to a derivation. -/
def toDualNumber {R : CompleteLocalAlgCat Λ k} (D : Derivation Λ R.carrier k) :
    R.carrier →ₐ[Λ] DualNumber k where
  toFun r := inl (algebraMap R.carrier k r) + inr (D r)
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry
  commutes' := sorry

/-- `toDualNumber D` evaluates to the dual number with scalar residue and infinitesimal `D`. -/
theorem toDualNumber_apply {R : CompleteLocalAlgCat Λ k} (D : Derivation Λ R.carrier k)
    (r : R.carrier) :
    toDualNumber D r = inl (algebraMap R.carrier k r) + inr (D r) := sorry

/-- The dual-number lift of a derivation, factored through the first maximal-adic truncation. -/
def toDualNumberHom (ξ : FormalObject p) (D : Derivation Λ ξ.base.carrier k) :
    ξ.base.truncation 1 ⟶ ArtinianLocalAlgCat.dualNumber Λ k where
  hom :=
    { toRingHom :=
        Ideal.Quotient.lift (maximalIdeal ξ.base.carrier ^ (1 + 1))
          (toDualNumber D).toRingHom sorry
      commutes' := sorry }
  isLocalHom := sorry
  residue_compat := sorry

/-- `toDualNumberHom` is the truncation of `toDualNumber` as a morphism of `C_Λ`. -/
theorem toDualNumberHom_spec (ξ : FormalObject p) (D : Derivation Λ ξ.base.carrier k)
    (r : ξ.base.carrier) :
    (toDualNumberHom ξ D).hom (Ideal.Quotient.mk (maximalIdeal ξ.base.carrier ^ (1 + 1)) r) =
      toDualNumber D r := sorry

/-- Opposite of the stagewise lying-over equality of a formal object. -/
theorem over_obj_op (ξ : FormalObject p) (n : ℕ) :
    p.op.obj (Opposite.op (ξ.system.family n)) = Opposite.op (ξ.base.truncation n) := sorry

/-- Cofibered pushforward of the first truncation of `ξ` along the dual-number lift of `D`. -/
def pushforwardDualNumber (ξ : FormalObject p) [IsPredeformationCategory p]
    (D : Derivation Λ ξ.base.carrier k) : F :=
  Opposite.unop (IsPreFibered.pullbackObj (over_obj_op ξ 1) (toDualNumberHom ξ D).op)

/-- The dual-number pushforward of the first stage of `ξ` lies over the dual numbers. -/
theorem pushforwardDualNumber_obj (ξ : FormalObject p) [IsPredeformationCategory p]
    (D : Derivation Λ ξ.base.carrier k) :
    p.obj (pushforwardDualNumber ξ D) = ArtinianLocalAlgCat.dualNumber Λ k := sorry

/-- The differential `dξ̲` sends a derivation to the isomorphism class of the dual-number
pushforward of the first truncation of `ξ`. -/
def differential (ξ : FormalObject p) [IsPredeformationCategory p] :
    Derivation Λ ξ.base.carrier k → Functor.tangentSpace p :=
  fun D ↦ tangentSpace.mk p (Fiber.mk (pushforwardDualNumber_obj ξ D))

/-- `differential ξ D` is the isomorphism class of the pushforward of `ξ.system.family 1`
along `toDualNumberHom ξ D`. -/
theorem differential_spec (ξ : FormalObject p) [IsPredeformationCategory p]
    (D : Derivation Λ ξ.base.carrier k) :
    differential ξ D = tangentSpace.mk p (Fiber.mk (pushforwardDualNumber_obj ξ D)) := sorry

end FormalObject

end
