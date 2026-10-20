/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import ReasLib.CategoryTheory.Fibered.Fiber.Isomorphism
public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.TangentSpace

/-!
# Identity-tangent comparison under residue pushforward

A specified residue-field pushforward induces a canonical comparison of
selected dual-number pushforwards. Conjugation restricts to the identity-tangent
subgroups and is linear for their canonical vector-space structures.
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

variable (p : F ⥤ ArtinianLocalAlgCat Λ k)

/-- The selected residue-field pushforward `x0` of `x`. -/
def residuePushforward [p.op.IsFibered] (x : F) : p.Fiber (residue Λ k) :=
  pushforwardObj p (toResidue (p.obj x)) (ofObj p x)

/-- `residuePushforward p x` is the selected pushforward along `toResidue`. -/
theorem residuePushforward_eq [p.op.IsFibered] (x : F) :
    residuePushforward p x =
      pushforwardObj p (toResidue (p.obj x)) (ofObj p x) := rfl

/-- The total-category object underlying the selected residue pushforward. -/
abbrev residuePushforwardObj [p.op.IsFibered] (x : F) : F :=
  fiberInclusion.obj (residuePushforward p x)

/-- `residuePushforwardObj` is the underlying object of `residuePushforward`. -/
theorem residuePushforwardObj_eq [p.op.IsFibered] (x : F) :
    residuePushforwardObj p x = (residuePushforward p x).1 := rfl

/-- The selected residue pushforward lies over `k`. -/
theorem residuePushforwardObj_property [p.op.IsFibered] (x : F) :
    p.obj (residuePushforwardObj p x) = residue Λ k :=
  (residuePushforward p x).property

/-- The arrow obtained by following a specified residue pushforward with its
selected dual-number pushforward. -/
def idTangentSpacePushforwardHom [p.op.IsFibered] (x : F)
    (x0 : p.Fiber (residue Λ k)) (φ : x ⟶ fiberInclusion.obj x0) :
    x ⟶ (idTangentSpaceObj p (fiberInclusion.obj x0)).1 :=
  φ ≫ pushforwardHom p
    (toResidue (p.obj (fiberInclusion.obj x0)) ≫ residueToDualNumber Λ k)
    (ofObj p (fiberInclusion.obj x0))

/-- The composite through a residue-fibre pushforward is strongly cocartesian
over the normalized residue-then-dual-number map. -/
instance instIsStronglyCocartesian_idTangentSpacePushforwardHom [p.op.IsFibered]
    (x : F) (x0 : p.Fiber (residue Λ k)) (φ : x ⟶ fiberInclusion.obj x0)
    [p.IsStronglyCocartesian (toResidue (p.obj x)) φ] :
    p.IsStronglyCocartesian (toResidue (p.obj x) ≫ residueToDualNumber Λ k)
      (idTangentSpacePushforwardHom p x x0 φ) := sorry

/-- The canonical vertical comparison between a selected dual-number pushforward
and the dual-number pushforward through a specified residue pushforward. -/
def idTangentSpaceObjIsoOfPushforward [p.op.IsFibered]
    (x : F) (x0 : p.Fiber (residue Λ k)) (φ : x ⟶ fiberInclusion.obj x0)
    [p.IsStronglyCocartesian (toResidue (p.obj x)) φ] :
    idTangentSpaceObj p x ≅ idTangentSpaceObj p (fiberInclusion.obj x0) :=
  let f := toResidue (p.obj x) ≫ residueToDualNumber Λ k
  let τ := pushforwardHom p f (ofObj p x)
  let ψ := idTangentSpacePushforwardHom p x x0 φ
  let hτ : p.IsCocartesian f τ := inferInstance
  let hψ : p.IsCocartesian f ψ := inferInstance
  let hψlift : p.IsHomLift f ψ := inferInstance
  isoMk
    (@IsCocartesian.codomainUniqueUpToIso _ _ _ _ p _ _ _ _ f τ hτ _ ψ hψ)
    (@IsCocartesian.map_isHomLift _ _ _ _ p _ _ _ _ f τ hτ _ ψ hψlift)

/-- The canonical comparison factors the selected dual-number pushforward arrow
through the specified residue pushforward. -/
theorem idTangentSpaceObjIsoOfPushforward_fac [p.op.IsFibered]
    (x : F) (x0 : p.Fiber (residue Λ k)) (φ : x ⟶ fiberInclusion.obj x0)
    [p.IsStronglyCocartesian (toResidue (p.obj x)) φ] :
    pushforwardHom p (toResidue (p.obj x) ≫ residueToDualNumber Λ k) (ofObj p x) ≫
      (idTangentSpaceObjIsoOfPushforward p x x0 φ).hom.1 =
        idTangentSpacePushforwardHom p x x0 φ :=
  let f := toResidue (p.obj x) ≫ residueToDualNumber Λ k
  let τ := pushforwardHom p f (ofObj p x)
  let ψ := idTangentSpacePushforwardHom p x x0 φ
  let hτ : p.IsCocartesian f τ := inferInstance
  let hψlift : p.IsHomLift f ψ := inferInstance
  @IsCocartesian.fac _ _ _ _ p _ _ _ _ f τ hτ _ ψ hψlift

/-- Conjugation by the vertical dual-number comparison maps the identity-restriction
subgroup onto the identity-restriction subgroup of the residue pushforward. -/
theorem idTangentSpaceObjIsoOfPushforward_map_subgroup [IsFibered.InGroupoids p.op]
    (x : F) (x0 : p.Fiber (residue Λ k)) (φ : x ⟶ fiberInclusion.obj x0)
    [p.IsStronglyCocartesian (toResidue (p.obj x)) φ] :
    (idTangentSpace p x).map
      (Aut.autMulEquivOfIso (idTangentSpaceObjIsoOfPushforward p x x0 φ)).toMonoidHom =
        idTangentSpace p (fiberInclusion.obj x0) := sorry

/-- Canonical conjugation restricts to a multiplicative equivalence of
identity-tangent subgroups under residue pushforward. -/
def idTangentSpaceMulEquivOfPushforward [IsFibered.InGroupoids p.op]
    (x : F) (x0 : p.Fiber (residue Λ k)) (φ : x ⟶ fiberInclusion.obj x0)
    [p.IsStronglyCocartesian (toResidue (p.obj x)) φ] :
    idTangentSpace p x ≃* idTangentSpace p (fiberInclusion.obj x0) :=
  (MulEquiv.subgroupMap
    (Aut.autMulEquivOfIso (idTangentSpaceObjIsoOfPushforward p x x0 φ))
    (idTangentSpace p x)).trans
      (MulEquiv.subgroupCongr (idTangentSpaceObjIsoOfPushforward_map_subgroup p x x0 φ))

/-- The multiplicative comparison preserves the pullback-defined addition and
epsilon-scaling action. -/
theorem idTangentSpaceMulEquivOfPushforward_linear [HasRimSchlessinger p]
    (x : F) (x0 : p.Fiber (residue Λ k)) (φ : x ⟶ fiberInclusion.obj x0)
    [p.IsStronglyCocartesian (toResidue (p.obj x)) φ] :
    (∀ α β : idTangentSpace p x,
      idTangentSpaceMulEquivOfPushforward p x x0 φ (α + β) =
        idTangentSpaceMulEquivOfPushforward p x x0 φ α +
          idTangentSpaceMulEquivOfPushforward p x x0 φ β) ∧
    (∀ r : k, ∀ α : idTangentSpace p x,
      idTangentSpaceMulEquivOfPushforward p x x0 φ (r • α) =
        r • idTangentSpaceMulEquivOfPushforward p x x0 φ α) := sorry

/-- A specified residue pushforward induces a canonical linear equivalence of
identity-tangent spaces. -/
def idTangentSpaceLinearEquivOfPushforward [HasRimSchlessinger p]
    (x : F) (x0 : p.Fiber (residue Λ k)) (φ : x ⟶ fiberInclusion.obj x0)
    [p.IsStronglyCocartesian (toResidue (p.obj x)) φ] :
    idTangentSpace p x ≃ₗ[k] idTangentSpace p (fiberInclusion.obj x0) where
  toEquiv := (idTangentSpaceMulEquivOfPushforward p x x0 φ).toEquiv
  map_add' := (idTangentSpaceMulEquivOfPushforward_linear p x x0 φ).1
  map_smul' := (idTangentSpaceMulEquivOfPushforward_linear p x x0 φ).2

/-- The canonical linear comparison acts by conjugation along the vertical
comparison of the selected dual-number pushforwards. -/
theorem idTangentSpaceLinearEquivOfPushforward_apply [HasRimSchlessinger p]
    (x : F) (x0 : p.Fiber (residue Λ k)) (φ : x ⟶ fiberInclusion.obj x0)
    [p.IsStronglyCocartesian (toResidue (p.obj x)) φ] (α : idTangentSpace p x) :
    (idTangentSpaceLinearEquivOfPushforward p x x0 φ α :
      Aut (idTangentSpaceObj p (fiberInclusion.obj x0))) =
        Aut.autMulEquivOfIso (idTangentSpaceObjIsoOfPushforward p x x0 φ)
          (α : Aut (idTangentSpaceObj p x)) := rfl

/-- The vertical comparison with the dual-number pushforward of the selected
residue pushforward. -/
def idTangentSpaceObjIso [p.op.IsFibered] (x : F) :
    idTangentSpaceObj p x ≅ idTangentSpaceObj p (residuePushforwardObj p x) :=
  @idTangentSpaceObjIsoOfPushforward _ _ _ _ _ _ _ _ _ p inferInstance x
    (residuePushforward p x) (pushforwardHom p (toResidue (p.obj x)) (ofObj p x))
    (pushforwardHom.isStronglyCocartesian p (toResidue (p.obj x)) (ofObj p x))

/-- Conjugation along the selected residue comparison restricts to a multiplicative
equivalence of identity-tangent subgroups. -/
def idTangentSpaceMulEquiv [IsFibered.InGroupoids p.op] (x : F) :
    idTangentSpace p x ≃* idTangentSpace p (residuePushforwardObj p x) :=
  @idTangentSpaceMulEquivOfPushforward _ _ _ _ _ _ _ _ _ p inferInstance x
    (residuePushforward p x) (pushforwardHom p (toResidue (p.obj x)) (ofObj p x))
    (pushforwardHom.isStronglyCocartesian p (toResidue (p.obj x)) (ofObj p x))

/-- The selected multiplicative comparison is conjugation by the selected
vertical dual-number comparison. -/
theorem idTangentSpaceMulEquiv_apply [IsFibered.InGroupoids p.op] (x : F)
    (α : idTangentSpace p x) :
    (idTangentSpaceMulEquiv p x α : Aut (idTangentSpaceObj p (residuePushforwardObj p x))) =
      Aut.autMulEquivOfIso (idTangentSpaceObjIso p x) (α : Aut (idTangentSpaceObj p x)) := rfl

/-- The canonical linear equivalence with the identity-tangent space of the selected
residue pushforward. -/
def idTangentSpaceLinearEquiv [HasRimSchlessinger p] (x : F) :
    idTangentSpace p x ≃ₗ[k] idTangentSpace p (residuePushforwardObj p x) :=
  @idTangentSpaceLinearEquivOfPushforward _ _ _ _ _ _ _ _ _ p inferInstance x
    (residuePushforward p x) (pushforwardHom p (toResidue (p.obj x)) (ofObj p x))
    (pushforwardHom.isStronglyCocartesian p (toResidue (p.obj x)) (ofObj p x))

/-- The selected linear comparison acts by conjugation along the selected vertical
comparison of dual-number pushforwards. -/
theorem idTangentSpaceLinearEquiv_apply [HasRimSchlessinger p] (x : F)
    (α : idTangentSpace p x) :
    (idTangentSpaceLinearEquiv p x α : Aut (idTangentSpaceObj p (residuePushforwardObj p x))) =
      Aut.autMulEquivOfIso (idTangentSpaceObjIso p x) (α : Aut (idTangentSpaceObj p x)) := rfl

end CategoryTheory.Functor
