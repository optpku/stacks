module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Associated
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic

/-! # Degree-zero associated modules on algebraic spaces over affine schemes -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.Associated

variable {R : Type u} [CommRing R]
variable {X : AlgebraicSpace (Spec (CommRingCat.of R))}

/-- The functor sending an `R`-module to the associated `𝒪_X`-module `𝒪_X ⊗_R -`,
obtained by extending scalars along the structure morphism and applying `tensorOXFunctor`. -/
noncomputable def associatedFunctor
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R))))) :
    ModuleCat.{u} R ⥤ Modules X :=
  ModuleCat.extendScalars (Hom.globalSectionsMap f) ⋙ tensorOXFunctor X

/-- On objects, `associatedFunctor f` is `tensorOX` after extension of scalars along
`Hom.globalSectionsMap f`. -/
theorem associatedFunctor_obj
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    (N : ModuleCat.{u} R) :
    (associatedFunctor f).obj N =
      tensorOX X ((ModuleCat.extendScalars (Hom.globalSectionsMap f)).obj N) :=
  rfl

/-- The associated `𝒪_X`-module of `N`, placed in degree zero, has quasicoherent cohomology. -/
theorem single_mem
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    (N : ModuleCat.{u} R) :
    derivedQuasiCoherentModuleProperty X
      ((DerivedCategory.singleFunctor (Modules X) (0 : ℤ)).obj
        ((associatedFunctor f).obj N)) :=
  sorry

/-- The associated `𝒪_X`-module of `N`, regarded as a degree-zero object of `DerivedQCoh X`. -/
noncomputable def single
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    (N : ModuleCat.{u} R) : DerivedQCoh X :=
  ⟨(DerivedCategory.singleFunctor (Modules X) (0 : ℤ)).obj ((associatedFunctor f).obj N),
    single_mem f N⟩

/-- The underlying derived object of `single f N` is the associated `𝒪_X`-module placed in
degree zero. -/
theorem single_obj
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    (N : ModuleCat.{u} R) :
    (single f N).obj =
      (DerivedCategory.singleFunctor (Modules X) (0 : ℤ)).obj ((associatedFunctor f).obj N) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.Associated
