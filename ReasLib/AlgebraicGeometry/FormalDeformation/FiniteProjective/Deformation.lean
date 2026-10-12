/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import ReasLib.AlgebraicGeometry.FormalDeformation.FiniteProjective
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Over

/-!
# The deformation category of a finite-dimensional vector space

The residue-fibre object and its slice in the category of finite projective
modules over Artinian local algebras.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat.FiniteProjective

/-- The residue-fibre object associated to a finite-dimensional `k`-vector space. -/
def residueObject (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    (groupoids Λ k).p.Fiber (ArtinianLocalAlgCat.residue Λ k) :=
  ⟨mkObj (ArtinianLocalAlgCat.residue Λ k)
    (ModuleCat.FiniteProjective.of k (ModuleCat.of k V)), rfl⟩

/-- The slice forgetful functor at the residue-fibre object is a predeformation category. -/
instance instIsPredeformationCategory_deformationForget
    (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    Functor.IsPredeformationCategory
      (Over.forget (Functor.Fiber.fiberInclusion.obj (residueObject V)) ⋙
        (groupoids Λ k).p) :=
  Functor.instIsPredeformationCategory_overForget (groupoids Λ k).p (residueObject V)

/-- The slice forgetful functor at the residue-fibre object is cofibered in groupoids. -/
instance instInGroupoids_deformationForget
    (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    Functor.IsFibered.InGroupoids
      (Over.forget (Functor.Fiber.fiberInclusion.obj (residueObject V)) ⋙
        (groupoids Λ k).p).op :=
  (instIsPredeformationCategory_deformationForget V).isCofiberedInGroupoids

/-- The deformation category is the Grothendieck category of the residue-fibre slice. -/
def deformation (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (ArtinianLocalAlgCat Λ k) :=
  CofiberedCategoryOver.Groupoids.ofFunctor
    (Over.forget (Functor.Fiber.fiberInclusion.obj (residueObject V)) ⋙
      (groupoids Λ k).p)

/-- The total category of the deformation category is the corresponding over category. -/
theorem deformation_spec (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    (deformation V :
        CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (ArtinianLocalAlgCat Λ k)).total =
      Over (Functor.Fiber.fiberInclusion.obj
        (residueObject V :
          (groupoids Λ k).p.Fiber (ArtinianLocalAlgCat.residue Λ k))) := rfl

/-- The deformation projection is a predeformation category. -/
instance instIsPredeformationCategory_deformation
    (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    Functor.IsPredeformationCategory
      (deformation V :
          CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (ArtinianLocalAlgCat Λ k)).p :=
  instIsPredeformationCategory_deformationForget V

end ArtinianLocalAlgCat.FiniteProjective
