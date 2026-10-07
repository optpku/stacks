module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- A nonzero derived module with quasicoherent cohomology has nonzero derived global
cohomology in some degree after tensoring with a nonnegative tensor power of an ample
invertible module. -/
@[stacks 0BQR]
theorem exists_nonzero_twistedCohomology {X : Scheme.{u}} (L : X.Modules)
    [Scheme.Modules.Invertible L] [Scheme.Modules.IsAmple L]
    (K : Scheme.ModuleDerived.Quasicoherent X) (hK : ¬ IsZero K) :
    ∃ (n : ℕ) (p : ℤ),
      ¬ IsZero ((RingedSpace.moduleDerivedCohomologyFunctor X.toRingedSpace p).obj
        (K.obj ⊗ᴸ (DerivedCategory.singleFunctor X.Modules 0).obj
          (RingedSpace.TensorPower.sheaf L n))) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
