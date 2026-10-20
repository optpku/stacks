module

public import Mathlib.Algebra.Module.Equiv.Defs
public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.TangentSpace
public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.Comparison

/-!
# The k-module structure on infinitesimal automorphisms

If `p : F ⥤ ArtinianLocalAlgCat Λ k` is cofibered in groupoids and satisfies
(RS), then `infinitesimalAutomorphismsAt p x0 x0' φ` is canonically identified
with `idTangentSpace p (fiberInclusion.obj x0)` and therefore carries the
natural `k`-vector space structure, with addition given by
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

/-- On the identity-tangent pushforward, infinitesimal automorphisms form exactly
the identity-restriction subgroup. -/
theorem infinitesimalAutomorphismsAt_eq_idTangentSpace
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (x0 : p.Fiber (residue Λ k)) :
    infinitesimalAutomorphismsAt p x0
        (idTangentSpaceObj p (fiberInclusion.obj x0)) (infAutIdTangentHom p x0) =
      idTangentSpace p (fiberInclusion.obj x0) := sorry

/-- Fibre identification of a dual-number pushforward of `x0` with the
identity-tangent Aut-carrier of `fiberInclusion.obj x0`. -/
def infAutCarrierIso
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    x0' ≅ idTangentSpaceObj p (fiberInclusion.obj x0) :=
  fiberIso_of_pushforward p φ (infAutIdTangentHom p x0)

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

/-- `Inf_{x0}(F)` is canonically isomorphic, as a group, to `T_id Aut(x0)`. -/
def infinitesimalAutomorphismsAtMulEquiv
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    infinitesimalAutomorphismsAt p x0 x0' φ ≃*
      idTangentSpace p (fiberInclusion.obj x0) := by
  let e := Aut.autMulEquivOfIso (infAutCarrierIso p x0 x0' φ)
  exact
    { toFun := fun α => ⟨e α.val,
        (mem_infinitesimalAutomorphismsAt_iff_mem_idTangentSpace p x0 x0' φ α.val).mp
          α.property⟩
      invFun := fun β => ⟨e.symm β.val,
        (mem_infinitesimalAutomorphismsAt_iff_mem_idTangentSpace p x0 x0' φ
          (e.symm β.val)).mpr (by
            change e (e.symm β.val) ∈ idTangentSpace p (fiberInclusion.obj x0)
            rw [e.apply_symm_apply]
            exact β.property)⟩
      left_inv := fun α => Subtype.ext (e.symm_apply_apply α.val)
      right_inv := fun β => Subtype.ext (e.apply_symm_apply β.val)
      map_mul' := fun α β => Subtype.ext (e.map_mul α.val β.val) }

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
      Aut.autMulEquivOfIso (infAutCarrierIso p x0 x0' φ) (α : Aut x0') := rfl

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
    (0 : infinitesimalAutomorphismsAt p x0 x0' φ) = 1 := rfl

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
    -α = α⁻¹ := rfl

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
        (r • infinitesimalAutomorphismsAtMulEquiv p x0 x0' φ α) := rfl

/-- Scalar multiplication on `infinitesimalAutomorphismsAt`. -/
instance instSMul_infinitesimalAutomorphismsAt
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    SMul k (infinitesimalAutomorphismsAt p x0 x0' φ) where
  smul := infinitesimalAutomorphismsAtSMul p x0 x0' φ

/-- Multiplication, identity, and inversion on infinitesimal automorphisms
satisfy the commutative additive group laws. -/
theorem infinitesimalAutomorphismsAt_addCommGroup_laws
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    (∀ α β γ : infinitesimalAutomorphismsAt p x0 x0' φ,
      (α + β) + γ = α + (β + γ)) ∧
    (∀ α : infinitesimalAutomorphismsAt p x0 x0' φ, 0 + α = α) ∧
    (∀ α : infinitesimalAutomorphismsAt p x0 x0' φ, α + 0 = α) ∧
    (∀ α : infinitesimalAutomorphismsAt p x0 x0' φ, -α + α = 0) ∧
    (∀ α β : infinitesimalAutomorphismsAt p x0 x0' φ, α + β = β + α) := sorry

/-- The additive group structure on infinitesimal automorphisms. -/
instance instAddCommGroup_infinitesimalAutomorphismsAt
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    AddCommGroup (infinitesimalAutomorphismsAt p x0 x0' φ) where
  add_assoc := (infinitesimalAutomorphismsAt_addCommGroup_laws p x0 x0' φ).1
  zero_add := (infinitesimalAutomorphismsAt_addCommGroup_laws p x0 x0' φ).2.1
  add_zero := (infinitesimalAutomorphismsAt_addCommGroup_laws p x0 x0' φ).2.2.1
  nsmul := nsmulRec
  neg_add_cancel := (infinitesimalAutomorphismsAt_addCommGroup_laws p x0 x0' φ).2.2.2.1
  zsmul := zsmulRec
  add_comm := (infinitesimalAutomorphismsAt_addCommGroup_laws p x0 x0' φ).2.2.2.2

/-- The transported tangent-space scalar action satisfies the module laws
for composition-defined addition. -/
theorem infinitesimalAutomorphismsAt_module_laws
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    (∀ α : infinitesimalAutomorphismsAt p x0 x0' φ, (1 : k) • α = α) ∧
    (∀ r s : k, ∀ α : infinitesimalAutomorphismsAt p x0 x0' φ,
      (r * s) • α = r • s • α) ∧
    (∀ r : k, r • (0 : infinitesimalAutomorphismsAt p x0 x0' φ) = 0) ∧
    (∀ r : k, ∀ α β : infinitesimalAutomorphismsAt p x0 x0' φ,
      r • (α + β) = r • α + r • β) ∧
    (∀ r s : k, ∀ α : infinitesimalAutomorphismsAt p x0 x0' φ,
      (r + s) • α = r • α + s • α) ∧
    (∀ α : infinitesimalAutomorphismsAt p x0 x0' φ, (0 : k) • α = 0) := sorry

/-- The natural `k`-vector space structure on infinitesimal automorphisms. -/
instance instModule_infinitesimalAutomorphismsAt
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    Module k (infinitesimalAutomorphismsAt p x0 x0' φ) where
  one_smul := (infinitesimalAutomorphismsAt_module_laws p x0 x0' φ).1
  mul_smul := (infinitesimalAutomorphismsAt_module_laws p x0 x0' φ).2.1
  smul_zero := (infinitesimalAutomorphismsAt_module_laws p x0 x0' φ).2.2.1
  smul_add := (infinitesimalAutomorphismsAt_module_laws p x0 x0' φ).2.2.2.1
  add_smul := (infinitesimalAutomorphismsAt_module_laws p x0 x0' φ).2.2.2.2.1
  zero_smul := (infinitesimalAutomorphismsAt_module_laws p x0 x0' φ).2.2.2.2.2

/-- Addition in the infinitesimal-automorphism `k`-module agrees with composition
in `Aut`. -/
theorem infinitesimalAutomorphismsAt_add_eq_mul
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    (α β : infinitesimalAutomorphismsAt p x0 x0' φ) :
    α + β = α * β := rfl

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
  map_add' α β := by
    change infinitesimalAutomorphismsAtMulEquiv p x0 x0' φ (α * β) = _
    rw [(infinitesimalAutomorphismsAtMulEquiv p x0 x0' φ).map_mul,
      idTangentSpace_add_eq_mul p]
    rfl
  map_smul' r α := by
    change infinitesimalAutomorphismsAtMulEquiv p x0 x0' φ
      ((infinitesimalAutomorphismsAtMulEquiv p x0 x0' φ).symm
        (r • infinitesimalAutomorphismsAtMulEquiv p x0 x0' φ α)) = _
    exact (infinitesimalAutomorphismsAtMulEquiv p x0 x0' φ).apply_symm_apply _
  left_inv := (infinitesimalAutomorphismsAtMulEquiv p x0 x0' φ).left_inv
  right_inv := (infinitesimalAutomorphismsAtMulEquiv p x0 x0' φ).right_inv

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
      Aut.autMulEquivOfIso (infAutCarrierIso p x0 x0' φ) (α : Aut x0') := rfl

end CategoryTheory.Functor
