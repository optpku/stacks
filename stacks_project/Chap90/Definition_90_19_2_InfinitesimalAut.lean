module

public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import stacks_project.Chap90.Definition_90_19_2_DualNumber

/-!
# Unique retraction of a dual-number pushforward

In a category cofibered in groupoids over `ArtinianLocalAlgCat Λ k`, a pushforward of a
residue-fibre object along `residueToDualNumber` admits a unique retraction over
`dualNumberToResidue` whose composite is the identity.
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
theorem isStronglyCocartesian_of_isCocartesian_inGroupoids
    {p : F ⥤ ArtinianLocalAlgCat Λ k} [IsFibered.InGroupoids p.op]
    {x y : F} {R S : ArtinianLocalAlgCat Λ k} {f : R ⟶ S} {φ : x ⟶ y}
    [p.IsCocartesian f φ] : p.IsStronglyCocartesian f φ := sorry

/-- The identity on a residue-fibre object lifts the composite `k ⟶ k[ε] ⟶ k`. -/
instance instIsHomLift_id_residueToDualNumber_comp
    {p : F ⥤ ArtinianLocalAlgCat Λ k} {x0 : p.Fiber (residue Λ k)} :
    p.IsHomLift (residueToDualNumber Λ k ≫ dualNumberToResidue Λ k)
      (𝟙 (fiberInclusion.obj x0)) := sorry

/-- The unique retraction of a chosen pushforward along `residueToDualNumber`, obtained from
the strongly cocartesian universal property applied to the identity on `x0`. -/
noncomputable def retraction (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] {x0 : p.Fiber (residue Λ k)}
    {x0' : p.Fiber (dualNumber Λ k)}
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    fiberInclusion.obj x0' ⟶ fiberInclusion.obj x0 :=
  IsStronglyCocartesian.map p (residueToDualNumber Λ k) φ
    (Eq.refl (residueToDualNumber Λ k ≫ dualNumberToResidue Λ k))
    (𝟙 (fiberInclusion.obj x0))

/-- The retraction of a dual-number pushforward lies over `dualNumberToResidue`. -/
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
    φ ≫ retraction p φ = 𝟙 (fiberInclusion.obj x0) := sorry

/-- A pushforward along `residueToDualNumber` admits a unique retraction over
`dualNumberToResidue` whose composite is the identity. -/
theorem existsUnique_retraction (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] {x0 : p.Fiber (residue Λ k)}
    {x0' : p.Fiber (dualNumber Λ k)}
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    ∃! χ : fiberInclusion.obj x0' ⟶ fiberInclusion.obj x0,
      p.IsHomLift (dualNumberToResidue Λ k) χ ∧
        φ ≫ χ = 𝟙 (fiberInclusion.obj x0) := sorry

end CategoryTheory.Functor
