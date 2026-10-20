module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

/-!
# The direct image of the structure sheaf in degree zero

For a quasi-compact, quasi-separated morphism of algebraic spaces, the underived
direct image of the structure sheaf defines a derived module with quasi-coherent
cohomology by placing it in degree zero.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The underived direct image `f_* 𝒪_X`, placed in degree zero, has quasi-coherent
cohomology for a quasi-compact, quasi-separated morphism of algebraic spaces. -/
theorem pushforwardStructureSheaf_mem (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    derivedQuasiCoherentModuleProperty Y
      ((DerivedCategory.singleFunctor (Modules Y) 0).obj
        (Modules.pushforwardStructureModule f)) :=
  sorry

/-- The underived direct image `f_* 𝒪_X`, placed in degree zero as a derived module
with quasi-coherent cohomology. -/
noncomputable def pushforwardStructureSheaf (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] : DerivedQCoh Y :=
  ⟨(DerivedCategory.singleFunctor (Modules Y) 0).obj
      (Modules.pushforwardStructureModule f),
    pushforwardStructureSheaf_mem f⟩

/-- The underlying derived module of `pushforwardStructureSheaf f` is the underived
direct image `f_* 𝒪_X`, placed in degree zero. -/
@[simp]
theorem pushforwardStructureSheaf_obj (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    (pushforwardStructureSheaf f).obj =
      (DerivedCategory.singleFunctor (Modules Y) 0).obj
        (Modules.pushforwardStructureModule f) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
