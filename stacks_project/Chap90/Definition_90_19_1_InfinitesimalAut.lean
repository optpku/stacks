module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import ReasLib.CategoryTheory.Fibered.Fiber.Isomorphism
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import stacks_project.Chap90.Definition_90_7_3_ArtinianLocal

/-!
# Infinitesimal automorphisms in a category cofibered in groupoids

If `p : F ⥤ ArtinianLocalAlgCat Λ k` is cofibered in groupoids and `φ` lies over
`f : A' ⟶ A`, the group of infinitesimal automorphisms of `x'` over `x` is the
equalizer subgroup of fibre automorphisms of `x'` that become the identity after
composing with `φ`. This coincides with the kernel of the induced map
`Aut (x') →* Aut (x)` along a cocartesian lift.
-/

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

open Fiber

/-- The group of infinitesimal automorphisms of a fibre object `x'` over `x` along a
morphism `φ` lying over `f`. As a subgroup of `Aut x'` it is the equalizer of
postcomposition with `φ`. -/
noncomputable def infinitesimalAut (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] {A' A : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A)
    {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ] :
    Subgroup (Aut x') where
  carrier := {α | fiberInclusion.map α.hom ≫ φ = φ}
  mul_mem' := sorry
  one_mem' := sorry
  inv_mem' := sorry

/-- Membership in `infinitesimalAut` is the equalizer condition that a fibre
automorphism of `x'` becomes the identity after composing with `φ`. -/
theorem mem_infinitesimalAut (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] {A' A : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A)
    {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    (α : Aut x') :
    α ∈ infinitesimalAut p f φ ↔ fiberInclusion.map α.hom ≫ φ = φ := sorry

/-- The induced homomorphism `Aut x' →* Aut x` on the fibres over `A'` and `A`,
sending a fibre automorphism of `x'` to the unique vertical automorphism of `x`
obtained from the cocartesian universal property of `φ`. -/
noncomputable def fiberAutHom (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] {A' A : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A)
    {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x)
    [p.IsHomLift f φ] [p.IsCocartesian f φ] :
    Aut x' →* Aut x where
  toFun α :=
    have h_hom : p.IsHomLift f (fiberInclusion.map α.hom ≫ φ) :=
      @CategoryTheory.IsHomLift.comp_lift_id_left _ _ _ _ p _ _ _ _ _ f φ _
        (fiberInclusion.map α.hom) α.hom.property
    have h_inv : p.IsHomLift f (fiberInclusion.map α.inv ≫ φ) :=
      @CategoryTheory.IsHomLift.comp_lift_id_left _ _ _ _ p _ _ _ _ _ f φ _
        (fiberInclusion.map α.inv) α.inv.property
    Fiber.isoMk
      { hom := @IsCocartesian.map _ _ _ _ p _ _ _ _ f φ _ _
          (fiberInclusion.map α.hom ≫ φ) h_hom
        inv := @IsCocartesian.map _ _ _ _ p _ _ _ _ f φ _ _
          (fiberInclusion.map α.inv ≫ φ) h_inv
        hom_inv_id := sorry
        inv_hom_id := sorry }
      (@IsCocartesian.map_isHomLift _ _ _ _ p _ _ _ _ f φ _ _
        (fiberInclusion.map α.hom ≫ φ) h_hom)
  map_one' := sorry
  map_mul' := sorry

/-- The induced fibre automorphism of `x` is characterized by the commutative square
`φ ≫ autMap(α) = α ≫ φ`. -/
theorem fiberAutHom_comp (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] {A' A : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A)
    {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x)
    [p.IsHomLift f φ] [p.IsCocartesian f φ] (α : Aut x') :
    φ ≫ fiberInclusion.map (fiberAutHom p f φ α).hom =
      fiberInclusion.map α.hom ≫ φ := sorry

/-- The equalizer subgroup `infinitesimalAut` is the kernel of `fiberAutHom`. -/
theorem infinitesimalAut_eq_ker (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] {A' A : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A)
    {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x)
    [p.IsHomLift f φ] [p.IsCocartesian f φ] :
    infinitesimalAut p f φ = (fiberAutHom p f φ).ker := sorry

end CategoryTheory.Functor
