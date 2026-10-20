/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.CategoryTheory.Endomorphism
public import ReasLib.AlgebraicGeometry.FormalDeformation.ContinuousRepresentation
public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Over

/-!
# Trivial dual-number lift of a continuous representation

Residue slices and scalar extension to the dual numbers for finite-dimensional
discrete-continuous representations.
-/

@[expose] public section

open CategoryTheory Functor
open scoped ChangeOfRings

noncomputable section

universe u

namespace ContinuousRep

section ToRepresentation

variable {Γ Λ k : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]

/-- The `End`-valued representation associated with the stored `GL`-action. -/
def toRepresentation (X : ContinuousRep Γ Λ k) :
    Representation X.base.carrier Γ X.module :=
  (Units.coeHom _).comp X.ρ

/-- Reconstructing the `GL`-valued action from `toRepresentation` recovers `ρ`. -/
theorem toRepresentation_asGroupHom (X : ContinuousRep Γ Λ k) :
    (toRepresentation X).asGroupHom = X.ρ := by
  apply MonoidHom.ext
  intro γ
  apply Units.ext
  rfl

end ToRepresentation

variable (Γ Λ k : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- `x0 = (k, V, ρ0)` as an object of the residue fibre of `forget`. -/
def residueObj (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) :
    (forget Γ Λ k).Fiber (ArtinianLocalAlgCat.residue Λ k) :=
  Fiber.mk (rfl : (forget Γ Λ k).obj (ofResidue Γ Λ k ρ0 hρ0) =
    ArtinianLocalAlgCat.residue Λ k)

/-- The underlying object of `residueObj` is `ofResidue`. -/
theorem residueObj_obj (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) :
    Fiber.fiberInclusion.obj (residueObj Γ Λ k ρ0 hρ0) = ofResidue Γ Λ k ρ0 hρ0 := rfl

/-- The forgetful projection of the slice over a residue representation. -/
abbrev deformationForget (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) :
    Over (Fiber.fiberInclusion.obj (residueObj Γ Λ k ρ0 hρ0)) ⥤
      ArtinianLocalAlgCat Λ k :=
  Over.forget (Fiber.fiberInclusion.obj (residueObj Γ Λ k ρ0 hρ0)) ⋙ forget Γ Λ k

/-- `deformationForget ρ0` is the composite of the Over-forgetful functor with `forget`. -/
theorem deformationForget_eq (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) :
    deformationForget Γ Λ k ρ0 hρ0 =
      Over.forget (Fiber.fiberInclusion.obj (residueObj Γ Λ k ρ0 hρ0)) ⋙
        forget Γ Λ k := rfl

/-- The trivial dual-number module `k[ε] ⊗_k V`. -/
abbrev trivialModule (V : Type u) [AddCommGroup V] [Module k V] : Type u :=
  (ModuleCat.extendScalars (ArtinianLocalAlgCat.residueToDualNumber Λ k).hom.toRingHom).obj
    (ModuleCat.of k V)

/-- The trivial dual-number module is scalar extension of the residue vector space. -/
theorem trivialModule_eq (V : Type u) [AddCommGroup V] [Module k V] :
    trivialModule Λ k V =
      (ModuleCat.extendScalars (ArtinianLocalAlgCat.residueToDualNumber Λ k).hom.toRingHom).obj
        (ModuleCat.of k V) := rfl

/-- Extension of scalars of a `k`-endomorphism of `V` to `trivialModule`. -/
def extendEnd (V : Type u) [AddCommGroup V] [Module k V] (ψ : Module.End k V) :
    Module.End (ArtinianLocalAlgCat.dualNumber Λ k).carrier (trivialModule Λ k V) :=
  ((ModuleCat.extendScalars (ArtinianLocalAlgCat.residueToDualNumber Λ k).hom.toRingHom).map
      (ModuleCat.ofHom ψ)).hom

/-- The extended endomorphism is the linear map obtained by the scalar-extension functor. -/
theorem extendEnd_eq (V : Type u) [AddCommGroup V] [Module k V] (ψ : Module.End k V) :
    extendEnd Λ k V ψ =
      ((ModuleCat.extendScalars (ArtinianLocalAlgCat.residueToDualNumber Λ k).hom.toRingHom).map
          (ModuleCat.ofHom ψ)).hom := rfl

/-- The `GL`-valued action of `Γ` on `k[ε] ⊗_k V` obtained by extending scalars of `ρ0`. -/
def trivialRho (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    Γ →* LinearMap.GeneralLinearGroup (ArtinianLocalAlgCat.dualNumber Λ k).carrier
      (trivialModule Λ k V) :=
  (Units.map
    ((ModuleCat.endRingEquiv
        ((ModuleCat.extendScalars (ArtinianLocalAlgCat.residueToDualNumber Λ k).hom.toRingHom).obj
          (ModuleCat.of k V))).toMonoidHom.comp
      ((Functor.mapEnd (ModuleCat.of k V)
          (ModuleCat.extendScalars (ArtinianLocalAlgCat.residueToDualNumber Λ k).hom.toRingHom)).comp
        (ModuleCat.endRingEquiv (ModuleCat.of k V)).symm.toMonoidHom))).comp ρ0

/-- The underlying linear map of `trivialRho ρ0 γ` is extension of scalars of `ρ0 γ`. -/
theorem trivialRho_apply (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (γ : Γ) :
    (trivialRho Γ Λ k ρ0 γ).val = extendEnd Λ k V (ρ0 γ).val := rfl

/-- Extending scalars of a discrete-continuous representation remains discrete-continuous. -/
theorem isContinuousDiscrete_trivialRho (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) :
    IsContinuousDiscrete (trivialRho Γ Λ k ρ0) := by
  sorry

/-- Scalar extension of a finite-dimensional vector space to the dual numbers is finite
projective over the dual numbers. -/
theorem trivialModule_finiteProjective :
    Module.FiniteProjective (ArtinianLocalAlgCat.dualNumber Λ k).carrier
      (trivialModule Λ k V) := by
  sorry

/-- The trivial dual-number object `(k[ε], k[ε] ⊗_k V, ρ0')` of `ContinuousRep`. -/
def trivialDeformationObj (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) :
    ContinuousRep Γ Λ k :=
  of (ArtinianLocalAlgCat.dualNumber Λ k)
    (ModuleCat.of (ArtinianLocalAlgCat.dualNumber Λ k).carrier (trivialModule Λ k V))
    (trivialModule_finiteProjective Λ k)
    (trivialRho Γ Λ k ρ0) (isContinuousDiscrete_trivialRho Γ Λ k ρ0 hρ0)

/-- The base of `trivialDeformationObj` is `k[ε]`. -/
theorem trivialDeformationObj_base (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) :
    (trivialDeformationObj Γ Λ k ρ0 hρ0).base = ArtinianLocalAlgCat.dualNumber Λ k := rfl

/-- The trivial dual-number deformation of `x0 = (k, V, ρ0)` in the fibre of `forget`. -/
def trivialDeformation (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) :
    (forget Γ Λ k).Fiber (ArtinianLocalAlgCat.dualNumber Λ k) :=
  Fiber.mk (rfl : (forget Γ Λ k).obj (trivialDeformationObj Γ Λ k ρ0 hρ0) =
    ArtinianLocalAlgCat.dualNumber Λ k)

/-- The underlying object of `trivialDeformation` is `trivialDeformationObj`. -/
theorem trivialDeformation_obj (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) :
    Fiber.fiberInclusion.obj (trivialDeformation Γ Λ k ρ0 hρ0) =
      trivialDeformationObj Γ Λ k ρ0 hρ0 := rfl

/-- The canonical inclusion `V → k[ε] ⊗_k V`, `v ↦ 1 ⊗ v`. -/
def trivialIncl (V : Type u) [AddCommGroup V] [Module k V] (v : V) : trivialModule Λ k V :=
  (1 : (ArtinianLocalAlgCat.dualNumber Λ k).carrier) ⊗ₜ[
    (ArtinianLocalAlgCat.residue Λ k).carrier,
    (ArtinianLocalAlgCat.residueToDualNumber Λ k).hom.toRingHom] v

/-- `trivialIncl` is the canonical tensor inclusion of `V`. -/
theorem trivialIncl_eq (V : Type u) [AddCommGroup V] [Module k V] (v : V) :
    trivialIncl Λ k V v =
      (1 : (ArtinianLocalAlgCat.dualNumber Λ k).carrier) ⊗ₜ[
        (ArtinianLocalAlgCat.residue Λ k).carrier,
        (ArtinianLocalAlgCat.residueToDualNumber Λ k).hom.toRingHom] v := rfl

private theorem trivialIncl_add (a b : V) :
    trivialIncl Λ k V (a + b) = trivialIncl Λ k V a + trivialIncl Λ k V b := by
  exact TensorProduct.tmul_add _ _ _

private theorem trivialIncl_smul (a : k) (v : V) :
    trivialIncl Λ k V (a • v) =
      ArtinianLocalAlgCat.Hom.toRingHom (ArtinianLocalAlgCat.residueToDualNumber Λ k) a •
        trivialIncl Λ k V v := by
  exact ((ModuleCat.extendRestrictScalarsAdj
    (ArtinianLocalAlgCat.residueToDualNumber Λ k).hom.toRingHom).unit.app
    (ModuleCat.of k V)).hom.map_smul a v

/-- The tensor inclusion intertwines the residue action and its scalar extension. -/
theorem trivialPushforward_equivariant
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0)
    (γ : Γ) (v : V) :
    trivialIncl Λ k V ((ρ0 γ).val v) =
      (trivialRho Γ Λ k ρ0 γ).val (trivialIncl Λ k V v) := by
  sorry

/-- The tensor inclusion induces the scalar-extension isomorphism. -/
theorem trivialPushforward_isBaseChange
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0) :
    IsBaseChangeAlong
      (X := ofResidue Γ Λ k ρ0 hρ0) (Y := trivialDeformationObj Γ Λ k ρ0 hρ0)
      (ArtinianLocalAlgCat.residueToDualNumber Λ k) (trivialIncl Λ k V)
      (by exact trivialIncl_add Λ k (V := V)) (by exact trivialIncl_smul Λ k (V := V)) := by
  sorry

/-- The canonical strongly cocartesian pushforward of `x0` along `k ⟶ k[ε]`. -/
def trivialPushforward (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) :
    Fiber.fiberInclusion.obj (residueObj Γ Λ k ρ0 hρ0) ⟶
      Fiber.fiberInclusion.obj (trivialDeformation Γ Λ k ρ0 hρ0) :=
  Hom.of (ArtinianLocalAlgCat.residueToDualNumber Λ k) (trivialIncl Λ k V)
    (by exact trivialIncl_add Λ k (V := V)) (by exact trivialIncl_smul Λ k (V := V))
    (trivialPushforward_equivariant Γ Λ k ρ0 hρ0)
    (trivialPushforward_isBaseChange Γ Λ k ρ0 hρ0)

/-- The base map of `trivialPushforward` is `residueToDualNumber`. -/
theorem trivialPushforward_base (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) :
    (forget Γ Λ k).map (trivialPushforward Γ Λ k ρ0 hρ0) =
      ArtinianLocalAlgCat.residueToDualNumber Λ k := rfl

/-- The canonical pushforward of `x0` along `k ⟶ k[ε]` is strongly cocartesian. -/
instance instIsStronglyCocartesian_trivialPushforward
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0) :
    (forget Γ Λ k).IsStronglyCocartesian (ArtinianLocalAlgCat.residueToDualNumber Λ k)
      (trivialPushforward Γ Λ k ρ0 hρ0) := by
  sorry

end ContinuousRep
