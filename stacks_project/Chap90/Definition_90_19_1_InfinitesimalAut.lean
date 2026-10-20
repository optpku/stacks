/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.InfinitesimalAutomorphisms
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

variable (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
variable {A' A : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A)
variable {x' : p.Fiber A'} {x : p.Fiber A}
variable (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
variable [p.IsCocartesian f φ]
variable (α : Aut x')

#check (CategoryTheory.Functor.infinitesimalAut p f φ : Subgroup (Aut x'))
#check (CategoryTheory.Functor.mem_infinitesimalAut p f φ α :
  α ∈ CategoryTheory.Functor.infinitesimalAut p f φ ↔
    fiberInclusion.map α.hom ≫ φ = φ)
#check (CategoryTheory.Functor.fiberAutHom p f φ : Aut x' →* Aut x)
#check (CategoryTheory.Functor.fiberAutHom_comp p f φ α :
  φ ≫ fiberInclusion.map (CategoryTheory.Functor.fiberAutHom p f φ α).hom =
    fiberInclusion.map α.hom ≫ φ)
#check (CategoryTheory.Functor.infinitesimalAut_eq_ker p f φ :
  CategoryTheory.Functor.infinitesimalAut p f φ =
    (CategoryTheory.Functor.fiberAutHom p f φ).ker)

end CategoryTheory.Functor
