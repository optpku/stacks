/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Module.Basic
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.DualNumberUnder
public import ReasLib.AlgebraicGeometry.FormalDeformation.AutomorphismFunctor

/-!
# Identity-tangent spaces of automorphism functors

The identity-restriction subgroup of dual-number automorphisms carries the
pullback-defined addition and epsilon-scaling action. Under the
Rim-Schlessinger condition these give a vector space whose addition equals
automorphism multiplication. Mathlib's multiplication of automorphisms reverses
categorical composition order; commutativity makes the two conventions agree.
-/

@[expose] public section

noncomputable section

open CategoryTheory hiding Linear
open CategoryTheory.Limits
open ArtinianLocalAlgCat

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

open Fiber Chosen ArtinianLocalAlgCat

variable (p : F ⥤ ArtinianLocalAlgCat Λ k)

/-- The selected dual-number pushforward of `x`, i.e. the fibre object
`(A → k[ε])_* x` whose automorphisms carry `T_id Aut(x)`. -/
abbrev idTangentSpaceObj [p.op.IsFibered] (x : F) : p.Fiber (dualNumber Λ k) :=
  pushforwardObj p (toResidue (p.obj x) ≫ residueToDualNumber Λ k) (ofObj p x)

/-- `idTangentSpaceObj` is the selected pushforward along `dualNumberUnder`. -/
theorem idTangentSpaceObj_eq [p.op.IsFibered] (x : F) :
    idTangentSpaceObj p x =
      pushforwardObj p (dualNumberUnder (p.obj x)).hom (ofObj p x) := rfl

/-- Automorphisms restricting to the identity are closed under multiplication,
identity, and inversion. -/
theorem idTangentSpace_laws [IsFibered.InGroupoids p.op] (x : F) :
    (∀ α β : Aut (idTangentSpaceObj p x),
      pushforwardAut p (dualNumberToResidueUnder (p.obj x)) (ofObj p x) α = 1 → pushforwardAut p (dualNumberToResidueUnder (p.obj x)) (ofObj p x) β = 1 →
      pushforwardAut p (dualNumberToResidueUnder (p.obj x)) (ofObj p x) (α * β) = 1) ∧
    pushforwardAut p (dualNumberToResidueUnder (p.obj x)) (ofObj p x) 1 = 1 ∧
    (∀ α : Aut (idTangentSpaceObj p x),
      pushforwardAut p (dualNumberToResidueUnder (p.obj x)) (ofObj p x) α = 1 → pushforwardAut p (dualNumberToResidueUnder (p.obj x)) (ofObj p x) α⁻¹ = 1) := sorry

/-- The identity-tangent space `T_id Aut(x)` is the fibre of `autFunctor p x` over
`A → k` inside `Aut ((A → k[ε])_* x)`. -/
def idTangentSpace [IsFibered.InGroupoids p.op] (x : F) :
    Subgroup (Aut (idTangentSpaceObj p x)) where
  carrier :=
    {α | pushforwardAut p (dualNumberToResidueUnder (p.obj x)) (ofObj p x) α =
      (1 : Aut (pushforwardObj p (toResidue (p.obj x)) (ofObj p x)))}
  mul_mem' := (idTangentSpace_laws p x).1 _ _
  one_mem' := (idTangentSpace_laws p x).2.1
  inv_mem' := (idTangentSpace_laws p x).2.2 _

/-- Membership in `idTangentSpace` is the identity-fibre condition for
`autFunctor.map` along `dualNumberToResidueUnder`. -/
theorem mem_idTangentSpace [IsFibered.InGroupoids p.op] (x : F)
    (α : Aut (idTangentSpaceObj p x)) :
    α ∈ idTangentSpace p x ↔
      pushforwardAut p (dualNumberToResidueUnder (p.obj x)) (ofObj p x) α =
        (1 : Aut (pushforwardObj p (toResidue (p.obj x)) (ofObj p x))) := Iff.rfl

/-- The underlying set of `idTangentSpace` is the identity fibre of `autFunctor`. -/
theorem idTangentSpace_def [IsFibered.InGroupoids p.op] (x : F) :
    (idTangentSpace p x : Set (Aut (idTangentSpaceObj p x))) =
      {α | pushforwardAut p (dualNumberToResidueUnder (p.obj x)) (ofObj p x) α =
        (1 : Aut (pushforwardObj p (toResidue (p.obj x)) (ofObj p x)))} := rfl

/-- Two identity-restriction automorphisms have the same residue restriction. -/
theorem idTangentSpaceAddPair_condition [IsFibered.InGroupoids p.op] {x : F}
    (α β : idTangentSpace p x) :
    (autFunctor p x).map (dualNumberToResidueUnder (p.obj x)) α.val =
      (autFunctor p x).map (dualNumberToResidueUnder (p.obj x)) β.val := sorry

/-- A matching pair of identity-tangent automorphisms, as an element of the type
pullback of the two dual-number restrictions. -/
def idTangentSpaceAddPair [IsFibered.InGroupoids p.op] {x : F}
    (α β : idTangentSpace p x) :
    Types.PullbackObj
      ((autFunctor p x).map (dualNumberToResidueUnder (p.obj x)))
      ((autFunctor p x).map (dualNumberToResidueUnder (p.obj x))) :=
  ⟨⟨α.val, β.val⟩, idTangentSpaceAddPair_condition p α β⟩

/-- The (RS) comparison equivalence for the dual-number square in `Under (p.obj x)`. -/
def idTangentSpaceAddEquiv [HasRimSchlessinger p] (x : F) :
    (autFunctor p x).obj (dualNumberPullbackUnder (p.obj x)) ≃
      Types.PullbackObj
        ((autFunctor p x).map (dualNumberToResidueUnder (p.obj x)))
        ((autFunctor p x).map (dualNumberToResidueUnder (p.obj x))) :=
  Equiv.ofBijective
    (autFunctorComparison p x
      (dualNumberToResidueUnder (p.obj x)) (dualNumberToResidueUnder (p.obj x))
      (dualNumberPullbackFstUnder (p.obj x)) (dualNumberPullbackSndUnder (p.obj x))
      (isPullback_dualNumberUnder (p.obj x)))
    (HasRimSchlessinger.autFunctorComparison_bijective p x
      (dualNumberToResidueUnder (p.obj x)) (dualNumberToResidueUnder (p.obj x))
      (dualNumberPullbackFstUnder (p.obj x)) (dualNumberPullbackSndUnder (p.obj x))
      (isPullback_dualNumberUnder (p.obj x))
      (dualNumberToResidueUnder_surjective (p.obj x)))

/-- The inverse pullback comparison followed by epsilon addition restricts to
the identity-restriction subgroup. -/
theorem idTangentSpaceAdd_mem [HasRimSchlessinger p] {x : F}
    (α β : idTangentSpace p x) :
    (autFunctor p x).map (dualNumberSumUnder (p.obj x))
      ((idTangentSpaceAddEquiv p x).symm (idTangentSpaceAddPair p α β)) ∈
        idTangentSpace p x := sorry

/-- Addition of identity-tangent automorphisms, via the (RS) inverse and
`dualNumberSumUnder`. -/
def idTangentSpaceAdd [HasRimSchlessinger p] {x : F}
    (α β : idTangentSpace p x) : idTangentSpace p x :=
  ⟨(autFunctor p x).map (dualNumberSumUnder (p.obj x))
      ((idTangentSpaceAddEquiv p x).symm (idTangentSpaceAddPair p α β)),
    idTangentSpaceAdd_mem p α β⟩

/-- `idTangentSpaceAdd` applies `autFunctor.map dualNumberSumUnder` to the (RS) inverse
of the matching pair. -/
theorem idTangentSpaceAdd_spec [HasRimSchlessinger p] {x : F}
    (α β : idTangentSpace p x) :
    (idTangentSpaceAdd p α β).val =
      (autFunctor p x).map (dualNumberSumUnder (p.obj x))
        ((idTangentSpaceAddEquiv p x).symm (idTangentSpaceAddPair p α β)) := rfl

/-- Epsilon scaling preserves automorphisms with identity residue restriction. -/
theorem idTangentSpaceSMul_mem [IsFibered.InGroupoids p.op] {x : F}
    (r : k) (α : idTangentSpace p x) :
    (autFunctor p x).map (dualNumberSMulUnder (p.obj x) r) α.val ∈
      idTangentSpace p x := sorry

/-- Scalar multiplication of identity-tangent automorphisms by dual-number scaling. -/
def idTangentSpaceSMul [IsFibered.InGroupoids p.op] {x : F}
    (r : k) (α : idTangentSpace p x) : idTangentSpace p x :=
  ⟨(autFunctor p x).map (dualNumberSMulUnder (p.obj x) r) α.val,
    idTangentSpaceSMul_mem p r α⟩

/-- `idTangentSpaceSMul r α` is `autFunctor.map` of `dualNumberSMulUnder r`. -/
theorem idTangentSpaceSMul_spec [IsFibered.InGroupoids p.op] {x : F}
    (r : k) (α : idTangentSpace p x) :
    (idTangentSpaceSMul p r α).val =
      (autFunctor p x).map (dualNumberSMulUnder (p.obj x) r) α.val := rfl

/-- Zero in the identity-tangent space is the identity automorphism. -/
instance instZero_idTangentSpace [IsFibered.InGroupoids p.op] (x : F) :
    Zero (idTangentSpace p x) where
  zero := 1

/-- The additive zero of `idTangentSpace` is the group identity. -/
theorem idTangentSpace_zero_eq_one [IsFibered.InGroupoids p.op] (x : F) :
    (0 : idTangentSpace p x) = 1 := rfl

/-- Negation on the identity-tangent space is inversion in `Aut`. -/
instance instNeg_idTangentSpace [IsFibered.InGroupoids p.op] (x : F) :
    Neg (idTangentSpace p x) where
  neg α := α⁻¹

/-- Additive inverse in `idTangentSpace` is the group inverse. -/
theorem idTangentSpace_neg_eq_inv [IsFibered.InGroupoids p.op] (x : F)
    (α : idTangentSpace p x) :
    -α = α⁻¹ := rfl

/-- Addition on `idTangentSpace`. -/
instance instAdd_idTangentSpace [HasRimSchlessinger p] (x : F) :
    Add (idTangentSpace p x) where
  add := idTangentSpaceAdd p

/-- Scalar multiplication on `idTangentSpace`. -/
instance instSMul_idTangentSpace [IsFibered.InGroupoids p.op] (x : F) :
    SMul k (idTangentSpace p x) where
  smul := idTangentSpaceSMul p

/-- The pullback-defined addition, identity zero, and inversion negation satisfy
the commutative additive group laws. -/
theorem idTangentSpace_addCommGroup_laws [HasRimSchlessinger p] (x : F) :
    (∀ α β γ : idTangentSpace p x, (α + β) + γ = α + (β + γ)) ∧
    (∀ α : idTangentSpace p x, 0 + α = α) ∧
    (∀ α : idTangentSpace p x, α + 0 = α) ∧
    (∀ α : idTangentSpace p x, -α + α = 0) ∧
    (∀ α β : idTangentSpace p x, α + β = β + α) := sorry

/-- The additive group structure on `T_id Aut(x)`. -/
instance instAddCommGroup_idTangentSpace [HasRimSchlessinger p] (x : F) :
    AddCommGroup (idTangentSpace p x) where
  add_assoc := (idTangentSpace_addCommGroup_laws p x).1
  zero_add := (idTangentSpace_addCommGroup_laws p x).2.1
  add_zero := (idTangentSpace_addCommGroup_laws p x).2.2.1
  nsmul := nsmulRec
  neg_add_cancel := (idTangentSpace_addCommGroup_laws p x).2.2.2.1
  zsmul := zsmulRec
  add_comm := (idTangentSpace_addCommGroup_laws p x).2.2.2.2

/-- Epsilon scaling satisfies the module laws for the pullback-defined addition. -/
theorem idTangentSpace_module_laws [HasRimSchlessinger p] (x : F) :
    (∀ α : idTangentSpace p x, (1 : k) • α = α) ∧
    (∀ r s : k, ∀ α : idTangentSpace p x, (r * s) • α = r • s • α) ∧
    (∀ r : k, r • (0 : idTangentSpace p x) = 0) ∧
    (∀ r : k, ∀ α β : idTangentSpace p x, r • (α + β) = r • α + r • β) ∧
    (∀ r s : k, ∀ α : idTangentSpace p x, (r + s) • α = r • α + s • α) ∧
    (∀ α : idTangentSpace p x, (0 : k) • α = 0) := sorry

/-- The natural `k`-vector space structure on `T_id Aut(x)`. -/
instance instModule_idTangentSpace [HasRimSchlessinger p] (x : F) :
    Module k (idTangentSpace p x) where
  one_smul := (idTangentSpace_module_laws p x).1
  mul_smul := (idTangentSpace_module_laws p x).2.1
  smul_zero := (idTangentSpace_module_laws p x).2.2.1
  smul_add := (idTangentSpace_module_laws p x).2.2.2.1
  add_smul := (idTangentSpace_module_laws p x).2.2.2.2.1
  zero_smul := (idTangentSpace_module_laws p x).2.2.2.2.2

/-- Addition in the identity-tangent `k`-module agrees with composition in `Aut`. -/
theorem idTangentSpace_add_eq_mul [HasRimSchlessinger p] {x : F}
    (α β : idTangentSpace p x) : α + β = α * β := sorry

/-- In particular, composition of identity-tangent automorphisms is commutative. -/
theorem idTangentSpace_mul_comm [HasRimSchlessinger p] {x : F}
    (α β : idTangentSpace p x) : α * β = β * α := by
  calc
    α * β = α + β := (idTangentSpace_add_eq_mul p α β).symm
    _ = β + α := add_comm α β
    _ = β * α := idTangentSpace_add_eq_mul p β α

end CategoryTheory.Functor
