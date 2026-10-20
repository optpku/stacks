module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.Equiv.Basic
public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms
public import ReasLib.AlgebraicGeometry.FormalDeformation.GroupRepresentation
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Over

/-!
# Trivial dual-number lift of a group representation

The residue-fibre slice projection of `Def_{V, ρ0}` and the trivial `k[ε]`-lift of a
finite-dimensional representation `ρ0`.
-/

@[expose] public section

open CategoryTheory Functor
open scoped ChangeOfRings

noncomputable section

universe u

namespace GroupRepCat

variable (Γ Λ k : Type u) [Group Γ] [CommRing Λ] [IsNoetherianRing Λ] [Field k]
  [Algebra Λ k] [Module.Finite Λ k]
variable {V : Type u} [AddCommGroup V] [Module k V] [finiteV : Module.Finite k V]

/-- The projection from residue-framed deformations to their base algebras. -/
abbrev deformationForget (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    deformation Γ Λ k ρ0 ⥤ ArtinianLocalAlgCat Λ k :=
  Over.forget (Fiber.fiberInclusion.obj (residueObj Γ Λ k ρ0)) ⋙ forget Γ Λ k

/-- `deformationForget ρ0` is the composite of the Over-forgetful functor with `forget`. -/
theorem deformationForget_eq (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    deformationForget Γ Λ k ρ0 =
      Over.forget (Fiber.fiberInclusion.obj (residueObj Γ Λ k ρ0)) ⋙ forget Γ Λ k := rfl

/-- The slice projection of `Def_{V, ρ0}` is a predeformation category. -/
instance instIsPredeformationCategory_deformationForget
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    IsPredeformationCategory (deformationForget Γ Λ k ρ0) :=
  instIsPredeformationCategory_overForget (forget Γ Λ k) (residueObj Γ Λ k ρ0)

/-- Predeformation categories are cofibered in groupoids. -/
instance instIsFiberedInGroupoids_deformationForget_op
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    IsFibered.InGroupoids (deformationForget Γ Λ k ρ0).op :=
  IsPredeformationCategory.isCofiberedInGroupoids

/-- The trivial dual-number module `k[ε] ⊗_k V`. -/
abbrev trivialModule (V : Type u) [AddCommGroup V] [Module k V] : Type u :=
  (ModuleCat.extendScalars (ArtinianLocalAlgCat.residueToDualNumber Λ k).hom.toRingHom).obj
    (ModuleCat.of k V)

/-- Unfolding of `trivialModule`. -/
theorem trivialModule_eq (V : Type u) [AddCommGroup V] [Module k V] :
    trivialModule Λ k V =
      (ModuleCat.extendScalars (ArtinianLocalAlgCat.residueToDualNumber Λ k).hom.toRingHom).obj
        (ModuleCat.of k V) := rfl

/-- Extension of scalars of a `k`-endomorphism of `V` to `trivialModule`. -/
def extendEnd (V : Type u) [AddCommGroup V] [Module k V] (ψ : Module.End k V) :
    Module.End (ArtinianLocalAlgCat.dualNumber Λ k).carrier (trivialModule Λ k V) :=
  ((ModuleCat.extendScalars (ArtinianLocalAlgCat.residueToDualNumber Λ k).hom.toRingHom).map
      (ModuleCat.ofHom (R := k) ψ)).hom

/-- Unfolding of `extendEnd`. -/
theorem extendEnd_eq (V : Type u) [AddCommGroup V] [Module k V] (ψ : Module.End k V) :
    extendEnd Λ k V ψ =
      ((ModuleCat.extendScalars (ArtinianLocalAlgCat.residueToDualNumber Λ k).hom.toRingHom).map
          (ModuleCat.ofHom (R := k) ψ)).hom := rfl

/-- The `GL`-valued action of `Γ` on `k[ε] ⊗_k V` obtained by extending scalars of `ρ0`. -/
def trivialRho (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    Γ →* LinearMap.GeneralLinearGroup (ArtinianLocalAlgCat.dualNumber Λ k).carrier
      (trivialModule Λ k V) := by
  have laws :
      (∀ γ, extendEnd Λ k V (ρ0 γ).val * extendEnd Λ k V (ρ0 γ).inv = 1) ∧
      (∀ γ, extendEnd Λ k V (ρ0 γ).inv * extendEnd Λ k V (ρ0 γ).val = 1) ∧
      extendEnd Λ k V (ρ0 1).val = 1 ∧
      (∀ γ δ, extendEnd Λ k V (ρ0 (γ * δ)).val =
        extendEnd Λ k V (ρ0 γ).val * extendEnd Λ k V (ρ0 δ).val) := sorry
  exact
    { toFun γ := ⟨extendEnd Λ k V (ρ0 γ).val, extendEnd Λ k V (ρ0 γ).inv,
        laws.1 γ, laws.2.1 γ⟩
      map_one' := Units.ext laws.2.2.1
      map_mul' γ δ := Units.ext (laws.2.2.2 γ δ) }

/-- The underlying linear map of `trivialRho ρ0 γ` is extension of scalars of `ρ0 γ`. -/
theorem trivialRho_apply (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (γ : Γ) :
    (trivialRho Γ Λ k ρ0 γ).val = extendEnd Λ k V (ρ0 γ).val := rfl

/-- The trivial dual-number object `(k[ε], k[ε] ⊗_k V, ρ0')` of `GroupRepCat`. -/
def trivialDeformationObj (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    GroupRepCat Γ Λ k := by
  have finiteProjective : Module.Finite k V →
      Module.FiniteProjective (ArtinianLocalAlgCat.dualNumber Λ k).carrier
        (trivialModule Λ k V) := sorry
  exact of (ArtinianLocalAlgCat.dualNumber Λ k) (trivialModule Λ k V)
    (finiteProjective finiteV) (trivialRho Γ Λ k ρ0)

/-- The base of `trivialDeformationObj` is `k[ε]`. -/
theorem trivialDeformationObj_base (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    (trivialDeformationObj Γ Λ k ρ0).base = ArtinianLocalAlgCat.dualNumber Λ k := rfl

/-- The trivial dual-number deformation of `x0 = (k, V, ρ0)` in the fibre of `forget`. -/
def trivialDeformation (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    (forget Γ Λ k).Fiber (ArtinianLocalAlgCat.dualNumber Λ k) :=
  ⟨trivialDeformationObj Γ Λ k ρ0, rfl⟩

/-- The underlying object of `trivialDeformation` is `trivialDeformationObj`. -/
theorem trivialDeformation_obj (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    Fiber.fiberInclusion.obj (trivialDeformation Γ Λ k ρ0) =
      trivialDeformationObj Γ Λ k ρ0 := rfl

/-- The canonical inclusion `V → k[ε] ⊗_k V`, `v ↦ 1 ⊗ v`. -/
def trivialIncl (V : Type u) [AddCommGroup V] [Module k V] (v : V) : trivialModule Λ k V :=
  (1 : (ArtinianLocalAlgCat.dualNumber Λ k).carrier) ⊗ₜ[
    k,
    (ArtinianLocalAlgCat.residueToDualNumber Λ k).hom.toRingHom] v

/-- `trivialIncl` is the canonical tensor inclusion of `V`. -/
theorem trivialIncl_eq (V : Type u) [AddCommGroup V] [Module k V] (v : V) :
    trivialIncl Λ k V v =
      (1 : (ArtinianLocalAlgCat.dualNumber Λ k).carrier) ⊗ₜ[
        k,
        (ArtinianLocalAlgCat.residueToDualNumber Λ k).hom.toRingHom] v := rfl

/-- The canonical strongly cocartesian pushforward of `x0` along `k ⟶ k[ε]`. -/
def trivialPushforward (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    Fiber.fiberInclusion.obj (residueObj Γ Λ k ρ0) ⟶
      Fiber.fiberInclusion.obj (trivialDeformation Γ Λ k ρ0) :=
  by
    let base := ArtinianLocalAlgCat.residueToDualNumber Λ k
    let t := trivialIncl Λ k V
    have laws :
        (∀ m n, t (m + n) = t m + t n) ∧
        (∀ (a : k) m, t (a • m) = ArtinianLocalAlgCat.Hom.toRingHom base a • t m) ∧
        (∀ γ m, t ((ρ0 γ).val m) = (trivialRho Γ Λ k ρ0 γ).val (t m)) ∧
        (∀ ha hs, IsIso (GroupRepCat.induced (X := ofResidue Γ Λ k ρ0)
          (Y := trivialDeformationObj Γ Λ k ρ0) base t ha hs)) := sorry
    exact Hom.of base t laws.1 laws.2.1 laws.2.2.1 (laws.2.2.2 _ _)

/-- The base map of `trivialPushforward` is `residueToDualNumber`. -/
theorem trivialPushforward_base (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    (forget Γ Λ k).map (trivialPushforward Γ Λ k ρ0) =
      ArtinianLocalAlgCat.residueToDualNumber Λ k := rfl

/-- The canonical pushforward of `x0` along `k ⟶ k[ε]` is strongly cocartesian. -/
instance instIsStronglyCocartesian_trivialPushforward
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    (forget Γ Λ k).IsStronglyCocartesian (ArtinianLocalAlgCat.residueToDualNumber Λ k)
      (trivialPushforward Γ Λ k ρ0) := sorry

end GroupRepCat
