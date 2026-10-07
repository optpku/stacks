module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import stacks_project.Chap90.Remark_90_6_4
public import stacks_project.Chap93.Example_93_4_1_Finite_projective_modules_Groupoids

/-!
# Residue fibre and deformation category of finite projective modules

The residue-fibre object `x₀ = (k, V)` and the slice `Def_V = F_{x₀}`.
-/

@[expose] public section

open CategoryTheory
open scoped Bicategory BasedFunctor

noncomputable section

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat.FiniteProjective

/-- The residue-fibre object `x₀ = (k, V)` in `F(k)`. -/
def residueObject (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    (groupoids Λ k).p.Fiber (ArtinianLocalAlgCat.residue Λ k) :=
  ⟨mkObj (ArtinianLocalAlgCat.residue Λ k)
    (ModuleCat.FiniteProjective.of k (ModuleCat.of k V)), rfl⟩

/-- The forgetful functor of the slice at `x₀ = (k, V)` is a predeformation category. -/
instance instIsPredeformationCategory_deformationForget
    (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    Functor.IsPredeformationCategory
      (Over.forget (Functor.Fiber.fiberInclusion.obj (residueObject V)) ⋙
        (groupoids Λ k).p) :=
  Functor.instIsPredeformationCategory_overForget (groupoids Λ k).p (residueObject V)

/-- The slice projection at `x₀` is cofibered in groupoids. -/
instance instInGroupoids_deformationForget
    (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    Functor.IsFibered.InGroupoids
      (Over.forget (Functor.Fiber.fiberInclusion.obj (residueObject V)) ⋙
        (groupoids Λ k).p).op :=
  (instIsPredeformationCategory_deformationForget V).isCofiberedInGroupoids

/-- The deformation category `Def_V = F_{x₀}` of a finite-dimensional `k`-vector space `V`. -/
def deformation (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (ArtinianLocalAlgCat Λ k) :=
  CofiberedCategoryOver.Groupoids.ofFunctor
    (Over.forget (Functor.Fiber.fiberInclusion.obj (residueObject V)) ⋙
      (groupoids Λ k).p)

/-- The total category of `Def_V` is the slice of `F` at `x₀ = (k, V)`. -/
theorem deformation_spec (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    (deformation V :
        CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (ArtinianLocalAlgCat Λ k)).total =
      Over (Functor.Fiber.fiberInclusion.obj
        (residueObject V :
          (groupoids Λ k).p.Fiber (ArtinianLocalAlgCat.residue Λ k))) := sorry

/-- The projection of `Def_V` is a predeformation category. -/
instance instIsPredeformationCategory_deformation
    (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    Functor.IsPredeformationCategory
      (deformation V :
          CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (ArtinianLocalAlgCat Λ k)).p :=
  instIsPredeformationCategory_deformationForget V

end ArtinianLocalAlgCat.FiniteProjective

