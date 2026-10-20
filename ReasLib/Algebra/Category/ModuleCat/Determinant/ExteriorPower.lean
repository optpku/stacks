module

public import ReasLib.Algebra.Category.ModuleCat.Determinant
public import ReasLib.Algebra.Category.ModuleCat.ExteriorPower.GradedProjection
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

@[expose] public section

open scoped Module.Determinant

noncomputable section

universe u v

namespace ModuleCat.Determinant

variable {R : Type u} [CommRing R]

/-- Projection from the determinant submodule to a chosen exterior degree. -/
noncomputable def topHom (M : ModuleCat.{v} R) (n : ℕ) :
    det[R](M) →ₗ[R] M.exteriorPower n :=
  (ModuleCat.exteriorPower.homogeneousProjection M n).comp
    (Module.Determinant.ι R M)

/-- For a finite free module of rank `n`, its `n`th exterior power lies in the determinant
submodule. -/
theorem topExteriorPower_le_determinant (M : ModuleCat.{v} R) (n : ℕ)
    [Module.Free R M] [Module.Finite R M]
    (hRank : Module.finrank R M = n) :
    (⋀[R]^n M) ≤ det[R](M) := sorry

/-- The canonical lift of the top exterior power into the determinant submodule. -/
noncomputable def topInv (M : ModuleCat.{v} R) (n : ℕ)
    [Module.Free R M] [Module.Finite R M]
    (hRank : Module.finrank R M = n) :
    M.exteriorPower n →ₗ[R] det[R](M) :=
  LinearMap.codRestrict det[R](M) (⋀[R]^n M).subtype
    (fun x ↦ topExteriorPower_le_determinant M n hRank x.property)

/-- Including a lifted top exterior element gives its usual inclusion in the exterior algebra. -/
theorem topInv_ι (M : ModuleCat.{v} R) (n : ℕ)
    [Module.Free R M] [Module.Finite R M]
    (hRank : Module.finrank R M = n) :
    (Module.Determinant.ι R M).comp (topInv M n hRank) =
      (⋀[R]^n M).subtype := sorry

/-- Projection after lifting is the identity on the top exterior power. -/
theorem topHom_topInv (M : ModuleCat.{v} R) (n : ℕ)
    [Module.Free R M] [Module.Finite R M]
    (hRank : Module.finrank R M = n) :
    (topHom M n).comp (topInv M n hRank) = LinearMap.id := sorry

/-- Lifting after projection is the identity on the determinant of a finite free module. -/
theorem topInv_topHom (M : ModuleCat.{v} R) (n : ℕ)
    [Module.Free R M] [Module.Finite R M]
    (hRank : Module.finrank R M = n) :
    (topInv M n hRank).comp (topHom M n) = LinearMap.id := sorry

/-- The determinant of a finite free rank-`n` module is its top exterior power. -/
noncomputable def topIso (M : ModuleCat.{v} R) (n : ℕ)
    [Module.Free R M] [Module.Finite R M]
    (hRank : Module.finrank R M = n) :
    det[R](M) ≃ₗ[R] M.exteriorPower n :=
  LinearEquiv.ofLinear (topHom M n) (topInv M n hRank)
    (topHom_topInv M n hRank) (topInv_topHom M n hRank)

/-- A map between equal-degree top exterior powers induces a map between determinant lines. -/
noncomputable def mapTopExteriorPower (M N : ModuleCat.{v} R) (n : ℕ)
    [Module.Free R M] [Module.Finite R M]
    [Module.Free R N] [Module.Finite R N]
    (hM : Module.finrank R M = n) (hN : Module.finrank R N = n) :
    (M.exteriorPower n →ₗ[R] N.exteriorPower n) →ₗ[R]
      (det[R](M) →ₗ[R] det[R](N)) where
  toFun f := (topIso N n hN).symm.toLinearMap.comp
    (f.comp (topIso M n hM).toLinearMap)
  map_add' f g := by ext; simp
  map_smul' r f := by ext; simp

/-- Evaluation of determinant transport is projection to the top exterior power, followed by
the given map and the canonical lift. -/
theorem mapTopExteriorPower_apply (M N : ModuleCat.{v} R) (n : ℕ)
    [Module.Free R M] [Module.Finite R M]
    [Module.Free R N] [Module.Finite R N]
    (hM : Module.finrank R M = n) (hN : Module.finrank R N = n)
    (f : M.exteriorPower n →ₗ[R] N.exteriorPower n) (z : det[R](M)) :
    mapTopExteriorPower M N n hM hN f z = topInv N n hN (f (topHom M n z)) := sorry

end ModuleCat.Determinant

end
