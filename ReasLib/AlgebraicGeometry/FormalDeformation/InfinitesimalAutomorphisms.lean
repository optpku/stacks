/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber.Section
public import ReasLib.CategoryTheory.Fibered.InfinitesimalAutomorphisms

/-!
# Infinitesimal automorphisms of a residue-fibre object

A chosen dual-number pushforward in a category cofibered in groupoids has a unique
retraction. Its relative automorphism subgroup is the group of infinitesimal automorphisms
of the residue-fibre object.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

open Fiber

/-- In a category cofibered in groupoids, every cocartesian lift is strongly cocartesian. -/
instance isStronglyCocartesian_of_isCocartesian_inGroupoids
    {p : F ⥤ ArtinianLocalAlgCat Λ k} [IsFibered.InGroupoids p.op]
    {x y : F} {R S : ArtinianLocalAlgCat Λ k} {f : R ⟶ S} {φ : x ⟶ y}
    [p.IsCocartesian f φ] : p.IsStronglyCocartesian f φ := sorry

/-- The identity on a residue-fibre object lifts the composite of inclusion and projection. -/
instance instIsHomLift_id_residueToDualNumber_comp
    {p : F ⥤ ArtinianLocalAlgCat Λ k} {x0 : p.Fiber (residue Λ k)} :
    p.IsHomLift (residueToDualNumber Λ k ≫ dualNumberToResidue Λ k)
      (𝟙 (fiberInclusion.obj x0)) :=
  (residueToDualNumber_comp_dualNumberToResidue Λ k).symm ▸
    CategoryTheory.IsHomLift.id (p := p) x0.property

/-- The retraction of a chosen dual-number pushforward, constructed by the strongly
cocartesian universal property applied to the identity on the residue-fibre object. -/
noncomputable def retraction (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] {x0 : p.Fiber (residue Λ k)}
    {x0' : p.Fiber (dualNumber Λ k)}
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    fiberInclusion.obj x0' ⟶ fiberInclusion.obj x0 :=
  IsStronglyCocartesian.map p (residueToDualNumber Λ k) φ
    (Eq.refl (residueToDualNumber Λ k ≫ dualNumberToResidue Λ k))
    (𝟙 (fiberInclusion.obj x0))

/-- The retraction of a dual-number pushforward lies over the coefficient projection. -/
instance retraction_isHomLift {p : F ⥤ ArtinianLocalAlgCat Λ k}
    [IsFibered.InGroupoids p.op] {x0 : p.Fiber (residue Λ k)}
    {x0' : p.Fiber (dualNumber Λ k)}
    {φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0'}
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    p.IsHomLift (dualNumberToResidue Λ k) (retraction p φ) :=
  IsStronglyCocartesian.map_isHomLift p (residueToDualNumber Λ k) φ
    (Eq.refl (residueToDualNumber Λ k ≫ dualNumberToResidue Λ k))
    (𝟙 (fiberInclusion.obj x0))

/-- The retraction of a dual-number pushforward is cocartesian. -/
instance retraction_isCocartesian {p : F ⥤ ArtinianLocalAlgCat Λ k}
    [IsFibered.InGroupoids p.op] {x0 : p.Fiber (residue Λ k)}
    {x0' : p.Fiber (dualNumber Λ k)}
    {φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0'}
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    p.IsCocartesian (dualNumberToResidue Λ k) (retraction p φ) := sorry

/-- The composite of a dual-number pushforward with its retraction is the identity. -/
theorem retraction_comp (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] {x0 : p.Fiber (residue Λ k)}
    {x0' : p.Fiber (dualNumber Λ k)}
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    φ ≫ retraction p φ = 𝟙 (fiberInclusion.obj x0) :=
  IsStronglyCocartesian.fac p (residueToDualNumber Λ k) φ
    (Eq.refl (residueToDualNumber Λ k ≫ dualNumberToResidue Λ k))
    (𝟙 (fiberInclusion.obj x0))

/-- A dual-number pushforward admits a unique retraction over the coefficient projection
whose composite with the pushforward is the identity. -/
theorem existsUnique_retraction (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] {x0 : p.Fiber (residue Λ k)}
    {x0' : p.Fiber (dualNumber Λ k)}
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    ∃! χ : fiberInclusion.obj x0' ⟶ fiberInclusion.obj x0,
      p.IsHomLift (dualNumberToResidue Λ k) χ ∧
        φ ≫ χ = 𝟙 (fiberInclusion.obj x0) :=
  IsStronglyCocartesian.universal_property p (residueToDualNumber Λ k) φ
    (dualNumberToResidue Λ k) (residueToDualNumber Λ k ≫ dualNumberToResidue Λ k) rfl
    (𝟙 (fiberInclusion.obj x0))

/-- The infinitesimal automorphisms of a residue-fibre object are the relative
automorphism subgroup of the retraction of its chosen dual-number pushforward. -/
@[stacks 06JQ]
noncomputable def infinitesimalAutomorphismsAt
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    Subgroup (Aut x0') :=
  infinitesimalAut p (dualNumberToResidue Λ k) (retraction p φ)

/-- Infinitesimal automorphisms form the kernel of fibre-automorphism restriction along
the retraction of the chosen dual-number pushforward. -/
theorem infinitesimalAutomorphismsAt_eq_ker
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    infinitesimalAutomorphismsAt p x0 x0' φ =
      (fiberAutHom p (dualNumberToResidue Λ k) (retraction p φ)).ker :=
  infinitesimalAut_eq_ker p (dualNumberToResidue Λ k) (retraction p φ)

/-- An automorphism is infinitesimal exactly when its fibre inclusion fixes the
retraction of the chosen dual-number pushforward. -/
theorem mem_infinitesimalAutomorphismsAt_iff
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] (α : Aut x0') :
    α ∈ infinitesimalAutomorphismsAt p x0 x0' φ ↔
      fiberInclusion.map α.hom ≫ retraction p φ = retraction p φ := Iff.rfl

end CategoryTheory.Functor
