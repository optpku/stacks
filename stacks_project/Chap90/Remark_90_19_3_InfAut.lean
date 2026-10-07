module

public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import ReasLib.CategoryTheory.Fibered.Fiber.Isomorphism
public import stacks_project.Chap90.Definition_90_19_2

/-!
# Canonical fibre isomorphisms of dual-number pushforwards

Any two strongly cocartesian lifts of `residueToDualNumber` have a unique vertical
comparison of targets, and a residue-fibre isomorphism induces such a comparison by
precomposition.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat
open Functor Fiber

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k)
variable [IsFibered.InGroupoids p.op]

namespace CategoryTheory.Functor

/-- A strongly cocartesian lift of `residueToDualNumber` is cocartesian. -/
instance instIsCocartesian_residueToDualNumber {x y : F}
    {φ : x ⟶ y} [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    p.IsCocartesian (residueToDualNumber Λ k) φ :=
  IsStronglyCocartesian.isCocartesian_of_isStronglyCocartesian p (residueToDualNumber Λ k) φ

/-- Precomposing a lift of `residueToDualNumber` with a residue-fibre morphism remains a
lift of `residueToDualNumber`. -/
instance isHomLift_comp_fiberHom
    {x0 y0 : p.Fiber (residue Λ k)} {y0' : p.Fiber (dualNumber Λ k)}
    (α : x0 ⟶ y0)
    (ψ : fiberInclusion.obj y0 ⟶ fiberInclusion.obj y0')
    [p.IsHomLift (residueToDualNumber Λ k) ψ] :
    p.IsHomLift (residueToDualNumber Λ k) (fiberInclusion.map α ≫ ψ) :=
  @IsHomLift.comp_lift_id_left _ _ _ _ p _ _ _ _ _ (residueToDualNumber Λ k) ψ
    inferInstance (fiberInclusion.map α) inferInstance

/-- The canonical vertical isomorphism between the targets of two dual-number pushforwards
of the same residue-fibre object, obtained from `IsCocartesian.codomainUniqueUpToIso`. -/
noncomputable def fiberIso_of_pushforward
    {x0 : p.Fiber (residue Λ k)} {x0' y0' : p.Fiber (dualNumber Λ k)}
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    (ψ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj y0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ] :
    x0' ≅ y0' :=
  isoMk
    (@IsCocartesian.codomainUniqueUpToIso _ _ _ _ p _ _ _ _ (residueToDualNumber Λ k) φ
      (IsStronglyCocartesian.isCocartesian_of_isStronglyCocartesian p (residueToDualNumber Λ k) φ)
      _ ψ
      (IsStronglyCocartesian.isCocartesian_of_isStronglyCocartesian p (residueToDualNumber Λ k) ψ))
    (@IsCocartesian.map_isHomLift _ _ _ _ p _ _ _ _ (residueToDualNumber Λ k) φ
      (IsStronglyCocartesian.isCocartesian_of_isStronglyCocartesian p (residueToDualNumber Λ k) φ)
      _ ψ inferInstance)

/-- The underlying total-category map of `fiberIso_of_pushforward` is the unique vertical
comparison of two cocartesian lifts. -/
theorem fiberIso_of_pushforward_hom
    {x0 : p.Fiber (residue Λ k)} {x0' y0' : p.Fiber (dualNumber Λ k)}
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    (ψ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj y0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ] :
    fiberInclusion.map (fiberIso_of_pushforward p φ ψ).hom =
      IsCocartesian.map p (residueToDualNumber Λ k) φ ψ := sorry

/-- The vertical isomorphism of dual-number pushforward targets induced by a residue-fibre
isomorphism, obtained by comparing `φ` with the precomposed pushforward of `α`. -/
noncomputable def fiberIso_of_fiberIso
    {x0 y0 : p.Fiber (residue Λ k)} {x0' y0' : p.Fiber (dualNumber Λ k)}
    (α : x0 ≅ y0)
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    (ψ : fiberInclusion.obj y0 ⟶ fiberInclusion.obj y0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ] :
    x0' ≅ y0' :=
  isoMk
    { hom := @IsCocartesian.map _ _ _ _ p _ _ _ _ (residueToDualNumber Λ k) φ inferInstance _
        (fiberInclusion.map α.hom ≫ ψ) (isHomLift_comp_fiberHom p α.hom ψ)
      inv := @IsCocartesian.map _ _ _ _ p _ _ _ _ (residueToDualNumber Λ k) ψ inferInstance _
        (fiberInclusion.map α.inv ≫ φ) (isHomLift_comp_fiberHom p α.inv φ)
      hom_inv_id := sorry
      inv_hom_id := sorry }
    (@IsCocartesian.map_isHomLift _ _ _ _ p _ _ _ _ (residueToDualNumber Λ k) φ inferInstance _
      (fiberInclusion.map α.hom ≫ ψ) (isHomLift_comp_fiberHom p α.hom ψ))

/-- The underlying total-category map of `fiberIso_of_fiberIso` is the unique vertical
factorization of the precomposed pushforward. -/
theorem fiberIso_of_fiberIso_hom
    {x0 y0 : p.Fiber (residue Λ k)} {x0' y0' : p.Fiber (dualNumber Λ k)}
    (α : x0 ≅ y0)
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    (ψ : fiberInclusion.obj y0 ⟶ fiberInclusion.obj y0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ] :
    fiberInclusion.map (fiberIso_of_fiberIso p α φ ψ).hom =
      @IsCocartesian.map _ _ _ _ p _ _ _ _ (residueToDualNumber Λ k) φ inferInstance _
        (fiberInclusion.map α.hom ≫ ψ) (isHomLift_comp_fiberHom p α.hom ψ) := sorry

end CategoryTheory.Functor
