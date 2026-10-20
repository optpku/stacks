module

public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms
import StacksCheckRecall

/-!
# Infinitesimal automorphisms of a residue-fibre object

The group `Inf_x0(F)` of infinitesimal automorphisms of an object `x0` in the residue fibre
of a category cofibered in groupoids over `C_Λ`.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

open Fiber

/- Definition 90.19.2. Let `p : F ⥤ ArtinianLocalAlgCat Λ k` be a category cofibered in
groupoids, and let `x0` be an object of the residue fibre `p.Fiber (residue Λ k)`. After a
choice of pushforward `φ` of `x0` along `residueToDualNumber`, there is a unique retraction
of `φ` over `dualNumberToResidue` whose composite is the identity on `x0`. The group of
infinitesimal automorphisms of `x0` is the relative group
`infinitesimalAut p (dualNumberToResidue Λ k) (retraction p φ)`. -/
@[stacks 06JQ] #check (CategoryTheory.Functor.infinitesimalAutomorphismsAt :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ],
    Subgroup (Aut x0'))

variable (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
  (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
  (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
  [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]

#check (CategoryTheory.Functor.retraction_comp p φ :
  φ ≫ retraction p φ = 𝟙 (fiberInclusion.obj x0))

#check (CategoryTheory.Functor.existsUnique_retraction p φ :
  ∃! χ : fiberInclusion.obj x0' ⟶ fiberInclusion.obj x0,
    p.IsHomLift (dualNumberToResidue Λ k) χ ∧ φ ≫ χ = 𝟙 (fiberInclusion.obj x0))

#check (CategoryTheory.Functor.infinitesimalAutomorphismsAt_eq_ker p x0 x0' φ :
  infinitesimalAutomorphismsAt p x0 x0' φ =
    (fiberAutHom p (dualNumberToResidue Λ k) (retraction p φ)).ker)

#check (CategoryTheory.Functor.mem_infinitesimalAutomorphismsAt_iff p x0 x0' φ :
  ∀ α : Aut x0', α ∈ infinitesimalAutomorphismsAt p x0 x0' φ ↔
    fiberInclusion.map α.hom ≫ retraction p φ = retraction p φ)

end CategoryTheory.Functor
