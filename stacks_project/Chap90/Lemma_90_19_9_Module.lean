module

public import Mathlib.Algebra.Module.Equiv.Defs
public import stacks_project.Chap90.Lemma_90_19_7_TangentSpace
public import stacks_project.Chap90.Remark_90_19_3

/-!
# The k-module structure on infinitesimal automorphisms

If `p : F ⥤ ArtinianLocalAlgCat Λ k` is cofibered in groupoids and satisfies
(RS), then `infinitesimalAutomorphismsAt p x0 x0' φ` is canonically identified
with `idTangentSpace p (fiberInclusion.obj x0)` and therefore carries the
natural `k`-vector space structure of Lemma 90.19.7, with addition given by
composition of automorphisms.
-/

@[expose] public section

noncomputable section

open CategoryTheory hiding Linear
open ArtinianLocalAlgCat

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

open Fiber Chosen

/-- The chosen cleavage lift of `x0` along `residueToDualNumber`, as a morphism
of underlying total-category objects of fibre objects. -/
def infAutChosenHom
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [p.op.IsFibered]
    (x0 : p.Fiber (residue Λ k)) :
    fiberInclusion.obj x0 ⟶
      fiberInclusion.obj (pushforwardObj p (residueToDualNumber Λ k) x0) :=
  pushforwardHom p (residueToDualNumber Λ k) x0

/-- `infAutChosenHom` is the selected cleavage lift `pushforwardHom`. -/
theorem infAutChosenHom_eq
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [p.op.IsFibered]
    (x0 : p.Fiber (residue Λ k)) :
    infAutChosenHom p x0 = pushforwardHom p (residueToDualNumber Λ k) x0 := sorry

/-- The selected dual-number lift of `fiberInclusion.obj x0` used by
`idTangentSpaceObj`. -/
def infAutIdTangentHom
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [p.op.IsFibered]
    (x0 : p.Fiber (residue Λ k)) :
    fiberInclusion.obj x0 ⟶
      fiberInclusion.obj (idTangentSpaceObj p (fiberInclusion.obj x0)) :=
  pushforwardHom p
    (toResidue (p.obj (fiberInclusion.obj x0)) ≫ residueToDualNumber Λ k)
    (ofObj p (fiberInclusion.obj x0))

/-- `infAutIdTangentHom` is the selected dual-number `pushforwardHom` of
`ofObj p (fiberInclusion.obj x0)`. -/
theorem infAutIdTangentHom_eq
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [p.op.IsFibered]
    (x0 : p.Fiber (residue Λ k)) :
    infAutIdTangentHom p x0 =
      pushforwardHom p
        (toResidue (p.obj (fiberInclusion.obj x0)) ≫ residueToDualNumber Λ k)
        (ofObj p (fiberInclusion.obj x0)) := sorry

/-- The chosen cleavage lift of `x0` is strongly cocartesian over
`residueToDualNumber`. -/
instance instIsStronglyCocartesian_infAutChosenHom
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [p.op.IsFibered]
    (x0 : p.Fiber (residue Λ k)) :
    p.IsStronglyCocartesian (residueToDualNumber Λ k) (infAutChosenHom p x0) :=
  pushforwardHom.isStronglyCocartesian p (residueToDualNumber Λ k) x0

/-- After identifying the residue fibre, the selected dual-number pushforward of
a residue-fibre object is strongly cocartesian over `residueToDualNumber`. -/
instance instIsStronglyCocartesian_infAutIdTangentHom
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [p.op.IsFibered]
    (x0 : p.Fiber (residue Λ k)) :
    p.IsStronglyCocartesian (residueToDualNumber Λ k) (infAutIdTangentHom p x0) :=
  sorry

/-- Fibre isomorphism between the chosen dual-number pushforward of `x0` and the
identity-tangent Aut-carrier `idTangentSpaceObj p (fiberInclusion.obj x0)`. -/
def infAutChosenIso_idTangentSpaceObj
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (x0 : p.Fiber (residue Λ k)) :
    pushforwardObj p (residueToDualNumber Λ k) x0 ≅
      idTangentSpaceObj p (fiberInclusion.obj x0) :=
  fiberIso_of_pushforward p (infAutChosenHom p x0) (infAutIdTangentHom p x0)

/-- `infAutChosenIso_idTangentSpaceObj` is the canonical vertical comparison of
the two dual-number lifts of `x0`. -/
theorem infAutChosenIso_idTangentSpaceObj_eq
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (x0 : p.Fiber (residue Λ k)) :
    infAutChosenIso_idTangentSpaceObj p x0 =
      fiberIso_of_pushforward p (infAutChosenHom p x0) (infAutIdTangentHom p x0) :=
  sorry

/-- Fibre identification of a dual-number pushforward of `x0` with the
identity-tangent Aut-carrier of `fiberInclusion.obj x0`. -/
def infAutCarrierIso
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    x0' ≅ idTangentSpaceObj p (fiberInclusion.obj x0) :=
  fiberIso_of_pushforward p φ (infAutChosenHom p x0) ≪≫
    infAutChosenIso_idTangentSpaceObj p x0

/-- `infAutCarrierIso` is the chosen-cleavage comparison followed by the
identity-tangent carrier comparison. -/
theorem infAutCarrierIso_eq
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    infAutCarrierIso p x0 x0' φ =
      fiberIso_of_pushforward p φ (infAutChosenHom p x0) ≪≫
        infAutChosenIso_idTangentSpaceObj p x0 := sorry

/-- `Inf_{x0}(F)` is canonically isomorphic, as a group, to `T_id Aut(x0)`. -/
def infinitesimalAutomorphismsAtMulEquiv
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    infinitesimalAutomorphismsAt p x0 x0' φ ≃*
      idTangentSpace p (fiberInclusion.obj x0) where
  toFun α := ⟨Aut.autMulEquivOfIso (infAutCarrierIso p x0 x0' φ) α.val, sorry⟩
  invFun β := ⟨(Aut.autMulEquivOfIso (infAutCarrierIso p x0 x0' φ)).symm β.val, sorry⟩
  left_inv := sorry
  right_inv := sorry
  map_mul' := sorry

/-- `infinitesimalAutomorphismsAtMulEquiv` acts by `Aut.autMulEquivOfIso` of
`infAutCarrierIso`. -/
theorem infinitesimalAutomorphismsAtMulEquiv_apply
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    (α : infinitesimalAutomorphismsAt p x0 x0' φ) :
    (infinitesimalAutomorphismsAtMulEquiv p x0 x0' φ α :
        Aut (idTangentSpaceObj p (fiberInclusion.obj x0))) =
      Aut.autMulEquivOfIso (infAutCarrierIso p x0 x0' φ) (α : Aut x0') := sorry

/-- Membership in `infinitesimalAutomorphismsAt` is membership in
`idTangentSpace` after conjugation along `infAutCarrierIso`. -/
theorem mem_infinitesimalAutomorphismsAt_iff_mem_idTangentSpace
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] (α : Aut x0') :
    α ∈ infinitesimalAutomorphismsAt p x0 x0' φ ↔
      Aut.autMulEquivOfIso (infAutCarrierIso p x0 x0' φ) α ∈
        idTangentSpace p (fiberInclusion.obj x0) := sorry

/-- Zero in `infinitesimalAutomorphismsAt` is the identity automorphism. -/
instance instZero_infinitesimalAutomorphismsAt
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    Zero (infinitesimalAutomorphismsAt p x0 x0' φ) where
  zero := 1

/-- The additive zero of `infinitesimalAutomorphismsAt` is the group identity. -/
theorem infinitesimalAutomorphismsAt_zero_eq_one
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    (0 : infinitesimalAutomorphismsAt p x0 x0' φ) = 1 := sorry

/-- Negation on `infinitesimalAutomorphismsAt` is inversion in `Aut`. -/
instance instNeg_infinitesimalAutomorphismsAt
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    Neg (infinitesimalAutomorphismsAt p x0 x0' φ) where
  neg α := α⁻¹

/-- Additive inverse in `infinitesimalAutomorphismsAt` is the group inverse. -/
theorem infinitesimalAutomorphismsAt_neg_eq_inv
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    (α : infinitesimalAutomorphismsAt p x0 x0' φ) :
    -α = α⁻¹ := sorry

/-- Addition on `infinitesimalAutomorphismsAt`. -/
instance instAdd_infinitesimalAutomorphismsAt
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    Add (infinitesimalAutomorphismsAt p x0 x0' φ) where
  add α β := α * β

/-- Scalar multiplication on `infinitesimalAutomorphismsAt`, transported from
`idTangentSpace` along `infinitesimalAutomorphismsAtMulEquiv`. -/
def infinitesimalAutomorphismsAtSMul
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    (r : k) (α : infinitesimalAutomorphismsAt p x0 x0' φ) :
    infinitesimalAutomorphismsAt p x0 x0' φ :=
  (infinitesimalAutomorphismsAtMulEquiv p x0 x0' φ).symm
    (r • infinitesimalAutomorphismsAtMulEquiv p x0 x0' φ α)

/-- `infinitesimalAutomorphismsAtSMul r α` is transport of `r • _` along
`infinitesimalAutomorphismsAtMulEquiv`. -/
theorem infinitesimalAutomorphismsAtSMul_spec
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    (r : k) (α : infinitesimalAutomorphismsAt p x0 x0' φ) :
    infinitesimalAutomorphismsAtSMul p x0 x0' φ r α =
      (infinitesimalAutomorphismsAtMulEquiv p x0 x0' φ).symm
        (r • infinitesimalAutomorphismsAtMulEquiv p x0 x0' φ α) := sorry

/-- Scalar multiplication on `infinitesimalAutomorphismsAt`. -/
instance instSMul_infinitesimalAutomorphismsAt
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    SMul k (infinitesimalAutomorphismsAt p x0 x0' φ) where
  smul := infinitesimalAutomorphismsAtSMul p x0 x0' φ

/-- The additive group structure on `Inf_{x0}(F)`. -/
instance instAddCommGroup_infinitesimalAutomorphismsAt
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    AddCommGroup (infinitesimalAutomorphismsAt p x0 x0' φ) where
  add_assoc := sorry
  zero_add := sorry
  add_zero := sorry
  nsmul := nsmulRec
  neg_add_cancel := sorry
  zsmul := zsmulRec
  add_comm := sorry

/-- The natural `k`-vector space structure on `Inf_{x0}(F)`. -/
instance instModule_infinitesimalAutomorphismsAt
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    Module k (infinitesimalAutomorphismsAt p x0 x0' φ) where
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

/-- Addition in the infinitesimal-automorphism `k`-module agrees with composition
in `Aut`. -/
theorem infinitesimalAutomorphismsAt_add_eq_mul
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    (α β : infinitesimalAutomorphismsAt p x0 x0' φ) :
    α + β = α * β := sorry

/-- The canonical `k`-linear isomorphism `Inf_{x0}(F) ≃ T_id Aut(x0)`. -/
def infinitesimalAutomorphismsAtLinearEquiv
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    infinitesimalAutomorphismsAt p x0 x0' φ ≃ₗ[k]
      idTangentSpace p (fiberInclusion.obj x0) where
  toFun := (infinitesimalAutomorphismsAtMulEquiv p x0 x0' φ).toFun
  invFun := (infinitesimalAutomorphismsAtMulEquiv p x0 x0' φ).invFun
  map_add' := sorry
  map_smul' := sorry
  left_inv := sorry
  right_inv := sorry

/-- The underlying Aut-map of `infinitesimalAutomorphismsAtLinearEquiv` is
conjugation along `infAutCarrierIso`. -/
theorem infinitesimalAutomorphismsAtLinearEquiv_apply
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    (α : infinitesimalAutomorphismsAt p x0 x0' φ) :
    (infinitesimalAutomorphismsAtLinearEquiv p x0 x0' φ α :
        Aut (idTangentSpaceObj p (fiberInclusion.obj x0))) =
      Aut.autMulEquivOfIso (infAutCarrierIso p x0 x0' φ) (α : Aut x0') := sorry

end CategoryTheory.Functor
