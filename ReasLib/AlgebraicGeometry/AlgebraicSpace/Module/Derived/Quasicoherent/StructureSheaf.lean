module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Tensor

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory ComplexShape ObjectProperty
open CategoryTheory.Pretriangulated

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}}

/-- The structure sheaf placed in degree zero has quasi-coherent cohomology. -/
theorem structureSheaf_mem (X : AlgebraicSpace S) :
    derivedQuasiCoherentModuleProperty X
      ((DerivedCategory.singleFunctor (Modules X) 0).obj
        (tensorUnit (Modules X))) :=
  sorry

/-- The structure sheaf `𝒪_X`, placed in degree zero, as a derived module with quasi-coherent
cohomology. This is the tensor unit of `Modules X`, the canonical owner of `K ⊗^L 𝒪_X`. -/
noncomputable def structureSheaf (X : AlgebraicSpace S) : DerivedQCoh X :=
  ⟨(DerivedCategory.singleFunctor (Modules X) 0).obj (tensorUnit (Modules X)),
    structureSheaf_mem X⟩

/-- The underlying derived module of the derived structure sheaf is the tensor unit placed in
degree zero. -/
theorem structureSheaf_obj (X : AlgebraicSpace S) :
    (structureSheaf X).obj =
      (DerivedCategory.singleFunctor (Modules X) 0).obj (tensorUnit (Modules X)) :=
  sorry

/-- The derived structure sheaf is canonically the degree-zero placement of the module tensor
unit. -/
noncomputable def structureSheafUnitIso (X : AlgebraicSpace S) :
    (structureSheaf X).obj ≅
      (DerivedCategory.singleFunctor (Modules X) 0).obj (tensorUnit (Modules X)) where
  hom := 𝟙 _
  inv := 𝟙 _

/-- The forward map of `structureSheafUnitIso` is the identity comparison of the degree-zero
unit complex. -/
theorem structureSheafUnitIso_hom (X : AlgebraicSpace S) :
    (structureSheafUnitIso X).hom = 𝟙 (structureSheaf X).obj :=
  sorry


end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
